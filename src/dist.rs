//! The distributed (MPI) backend, behind `--features hpc`.
//!
//! This is the real-transport counterpart of
//! [`crate::explore::verify_configuration_distributed_sim`]: where the
//! simulation hands continuation bytes between in-process "ranks", here actual
//! MPI processes (`mpirun -n N`) exchange them. Two axes are implemented:
//!
//! - [`outer_sweep_winner`] - the **outer configuration sweep across ranks**:
//!   each rank verifies its share of candidate configurations; an MPI
//!   all-reduce(min) selects the lowest-rank valid one (only a `u64` crosses).
//! - [`verify_configuration_mpi`] - the **inner frontier across ranks** for a
//!   single fixed configuration: a wave-synchronised search where each rank steps
//!   its share of the frontier, the successors are MPI all-gathered (so a
//!   continuation produced on one rank migrates to whichever rank owns it next),
//!   and the per-rank [`LocalAccumulators`] reduce by commutative union. The
//!   continuations are `serde`/`postcard` encoded - the real bytes a node ships.
//!
//! Building this needs a system MPI library (rsmpi links it via `mpicc`) and
//! libclang (rsmpi's bindgen); `build.rs` provisions both under `--features hpc`.
//! Run, for example: `mpirun -n 24 target/debug/formal mpi-selftest`.

#![cfg(feature = "hpc")]

use crate::ast::{Ast, AstNode};
use crate::explore::{candidate_configs, step_local, valid_path_to_local, verify_configuration};
use crate::verifier::{
    Continuation, ExplorePathResult, InnerVerifierConfiguration, LocalAccumulators, Terminal,
};
use crate::verifier_types::{State, TypeConfiguration};
use mpi::collective::SystemOperation;
use mpi::datatype::PartitionMut;
use mpi::traits::*;
use mpi::{Count, Tag};
use std::collections::{BTreeMap, VecDeque};
use std::ptr::NonNull;
use thousands::Separable;

fn internal(message: impl Into<String>) -> crate::verifier::CompilerError {
    crate::verifier::CompilerError::Internal(message.into())
}

/// Variable-count all-gather of a byte buffer: returns each rank's buffer (in
/// rank order). The standard MPI pattern - all-gather the lengths, compute
/// displacements, then `all_gather_varcount_into` the bytes. This is the one
/// primitive both the continuation migration and the accumulator reduce use.
fn all_gather_bytes<C: Communicator>(
    world: &C,
    send: &[u8],
) -> Result<Vec<Vec<u8>>, crate::verifier::CompilerError> {
    let size = world.size() as usize;

    let my_len: Count = send.len() as Count;
    let mut lengths: Vec<Count> = vec![0; size];
    world.all_gather_into(&my_len, &mut lengths[..]);

    let mut displacements: Vec<Count> = vec![0; size];
    let mut offset: Count = 0;
    for (i, &len) in lengths.iter().enumerate() {
        displacements[i] = offset;
        offset += len;
    }
    let mut received = vec![0u8; offset as usize];
    {
        let mut partition = PartitionMut::new(&mut received[..], &lengths[..], &displacements[..]);
        world.all_gather_varcount_into(send, &mut partition);
    }

    Ok((0..size)
        .map(|i| {
            let start = displacements[i] as usize;
            let end = start + lengths[i] as usize;
            received[start..end].to_vec()
        })
        .collect())
}

/// The outer configuration sweep across the MPI world. Rank `r` verifies the
/// candidates with `index % size == r`; the global lowest valid index (selected
/// by an all-reduce(min)) is the configuration the sequential oracle would infer.
///
/// # Safety
/// `ast_head` heads each rank's live (replicated) AST.
pub unsafe fn outer_sweep_winner<C: Communicator>(
    world: &C,
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    candidates: &[TypeConfiguration],
) -> Result<Option<usize>, crate::verifier::CompilerError> {
    let rank = world.rank() as usize;
    let size = world.size() as usize;

    let mut local_min: u64 = u64::MAX;
    for (i, configuration) in candidates.iter().enumerate() {
        if i % size == rank {
            if let ExplorePathResult::Valid(_) =
                verify_configuration(ast_head, systems, configuration)?
            {
                local_min = local_min.min(i as u64);
            }
        }
    }
    let mut winner: u64 = u64::MAX;
    world.all_reduce_into(&local_min, &mut winner, SystemOperation::min());
    Ok((winner != u64::MAX).then_some(winner as usize))
}

/// The inner search for one fixed `configuration`, distributed across the MPI
/// world with real continuation migration. Wave-synchronised: every rank holds
/// the (replicated) frontier, steps the continuations it owns (`index % size ==
/// rank`), and the successors are MPI all-gathered into the next frontier - so a
/// continuation produced on one rank is processed by whichever rank owns its slot
/// next (migration). Each continuation is stepped by exactly one rank, so the
/// per-rank [`LocalAccumulators`] are disjoint contributions that reduce by union.
/// Returns `Some(union)` if valid, `None` if any rank hit `Invalid`.
///
/// # Safety
/// `ast_head` heads each rank's live (replicated) AST.
pub unsafe fn verify_configuration_mpi<C: Communicator>(
    world: &C,
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
) -> Result<Option<LocalAccumulators>, crate::verifier::CompilerError> {
    let rank = world.rank() as usize;
    let size = world.size() as usize;

    let ast = Ast::index(ast_head);
    let start = ast
        .head()
        .ok_or_else(|| internal("verify_configuration_mpi: empty AST"))?;
    let start_id = ast
        .id_of(start)
        .ok_or_else(|| internal("verify_configuration_mpi: entry not indexed"))?;

    // The seed frontier is identical on every rank (deterministic construction),
    // which keeps the replicated frontier consistent without a scatter.
    let mut frontier: Vec<Continuation> = systems
        .iter()
        .map(|system| {
            let mut fronts = BTreeMap::new();
            for hart in 0..system.harts {
                fronts.insert(hart, start_id);
            }
            Continuation {
                state: State::new(system, configuration),
                fronts,
                active_hart: 0,
            }
        })
        .collect();

    let mut total = LocalAccumulators::default();

    loop {
        // Step the continuations this rank owns.
        let mut successors: Vec<Continuation> = Vec::new();
        let mut invalid: u8 = 0;
        for (i, cont) in frontier.iter().enumerate() {
            if i % size == rank {
                let (succ, terminal, local) = step_local(&ast, configuration, cont)?;
                total.union_with(local);
                if matches!(terminal, Some(Terminal::Invalid)) {
                    invalid = 1;
                }
                successors.extend(succ);
            }
        }

        // Any rank's `Invalid` invalidates the whole configuration.
        let mut any_invalid: u8 = 0;
        world.all_reduce_into(&invalid, &mut any_invalid, SystemOperation::max());
        if any_invalid != 0 {
            return Ok(None);
        }

        // Migrate: all-gather the successors so every rank rebuilds the identical
        // next frontier (concatenated in rank order).
        let encoded = postcard::to_stdvec(&successors)
            .map_err(|e| internal(format!("successor serialize: {e}")))?;
        let buffers = all_gather_bytes(world, &encoded)?;
        let mut next: Vec<Continuation> = Vec::new();
        for buffer in &buffers {
            let part: Vec<Continuation> = postcard::from_bytes(buffer)
                .map_err(|e| internal(format!("successor deserialize: {e}")))?;
            next.extend(part);
        }
        if next.is_empty() {
            break;
        }
        frontier = next;
    }

    // Reduce: union every rank's disjoint accumulator contribution.
    let encoded =
        postcard::to_stdvec(&total).map_err(|e| internal(format!("accumulator serialize: {e}")))?;
    let buffers = all_gather_bytes(world, &encoded)?;
    let mut global = LocalAccumulators::default();
    for buffer in &buffers {
        let part: LocalAccumulators = postcard::from_bytes(buffer)
            .map_err(|e| internal(format!("accumulator deserialize: {e}")))?;
        global.union_with(part);
    }
    Ok(Some(global))
}

/// A work message: a chunk of stolen continuations plus the Mattern credit that
/// travels with them (so credit is conserved as work migrates).
#[derive(serde::Serialize, serde::Deserialize)]
struct WorkMsg {
    continuations: Vec<Continuation>,
    credit: u64,
}

const TAG_STEAL: Tag = 1; // thief -> victim: "send me work"
const TAG_WORK: Tag = 2; // victim -> thief: a `WorkMsg`
const TAG_NOWORK: Tag = 3; // victim -> thief: "I have none"
const TAG_CREDIT: Tag = 4; // idle rank -> rank 0: returned credit (u64 LE)
const TAG_STOP: Tag = 5; // rank 0 -> all (or any -> all on Invalid): terminate

/// The total Mattern credit, held entirely by rank 0 at the start (it owns the
/// seed). Large and power-of-two so halving on each work hand-off never
/// underflows at any realistic steal depth.
const TOTAL_CREDIT: u64 = 1 << 40;

/// A typed empty payload for the control messages that carry no data.
const EMPTY: &[u8] = &[];

/// Per-rank work-stealing instrumentation, gathered to rank 0 at the end so a run
/// can report **utilisation** (how evenly the frontier spread, how much stealing
/// it cost). `serde` so it rides the same `all_gather_bytes` primitive as the
/// accumulators.
#[derive(serde::Serialize, serde::Deserialize, Clone, Default, Debug)]
pub struct RankStats {
    pub rank: i32,
    /// Continuations this rank stepped (its share of the search).
    pub processed: u64,
    /// `STEAL` requests this rank sent while idle.
    pub steals_sent: u64,
    /// Steals this rank served (handed half its deque to a thief).
    pub steals_served: u64,
    /// Work chunks this rank received from a victim.
    pub work_received: u64,
    /// Loop iterations this rank spent idle (deque empty).
    pub idle_iters: u64,
    /// Seconds this rank spent in the search loop.
    pub seconds: f64,
}

/// The inner search for one fixed `configuration`, distributed by **lifeline
/// work-stealing with Mattern credit termination detection** - the load-balanced
/// successor to the wave-synchronised [`verify_configuration_mpi`].
///
/// Each rank owns a local deque of continuations (rank 0 seeded with all of
/// them). A rank works its deque (step, push successors); when it empties, it
/// becomes a thief and sends a `STEAL` to a victim, cycling its **lifeline**
/// hypercube neighbours (`rank XOR 2^k`); a victim with surplus replies with half
/// its deque. There is no per-wave barrier, so a rank never idles waiting for the
/// slowest one - the load rebalances continuously.
///
/// Termination is detected with **Mattern's credit scheme**: the conserved total
/// credit starts at rank 0; work hand-offs carry half the sender's credit, and a
/// rank returns its credit to rank 0 when it goes idle. When rank 0 has all the
/// credit back it knows no rank holds work and none is in flight (credit travels
/// with work), so it broadcasts `STOP`. A reachable `#!` short-circuits with an
/// invalidating `STOP`. Continuations move (never copy) between deques, so each
/// is stepped exactly once and the per-rank [`LocalAccumulators`] are disjoint
/// contributions that reduce by commutative union.
///
/// # Safety
/// `ast_head` heads each rank's live (replicated) AST.
pub unsafe fn verify_configuration_mpi_stealing<C: Communicator>(
    world: &C,
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
    progress: bool,
) -> Result<Option<(LocalAccumulators, Vec<RankStats>)>, crate::verifier::CompilerError> {
    let rank = world.rank();
    let size = world.size();

    let ast = Ast::index(ast_head);
    let start_id = ast
        .id_of(
            ast.head()
                .ok_or_else(|| internal("verify_configuration_mpi_stealing: empty AST"))?,
        )
        .ok_or_else(|| internal("verify_configuration_mpi_stealing: entry not indexed"))?;

    // Rank 0 seeds all continuations and holds all the credit; others start empty.
    let mut deque: VecDeque<Continuation> = VecDeque::new();
    let mut credit: u64 = 0;
    if rank == 0 {
        for system in systems {
            let mut fronts = BTreeMap::new();
            for hart in 0..system.harts {
                fronts.insert(hart, start_id);
            }
            deque.push_back(Continuation {
                state: State::new(system, configuration),
                fronts,
                active_hart: 0,
            });
        }
        credit = TOTAL_CREDIT;
    }

    // Lifeline victims: the hypercube neighbours of this rank.
    let lifelines: Vec<i32> = (0..)
        .map(|k| 1i32 << k)
        .take_while(|&d| d < size)
        .map(|d| rank ^ d)
        .filter(|&v| v < size)
        .collect();

    let mut total = LocalAccumulators::default();
    let mut home: u64 = 0; // rank 0: credit returned so far (plus its own when idle)
    let mut returned = false; // returned our credit since last becoming active?
    let mut outstanding_steal = false;
    let mut victim_idx = 0usize;
    let mut invalid = false;

    // Utilisation counters + a throttle for the optional live progress lines.
    let mut stats = RankStats {
        rank,
        ..Default::default()
    };
    let started = std::time::Instant::now();
    let mut last_print = started;

    'run: loop {
        if progress && last_print.elapsed() >= std::time::Duration::from_millis(250) {
            last_print = std::time::Instant::now();
            println!(
                "[rank {rank} t={:.2}s] processed={} deque={} steals_sent={} work_received={}",
                started.elapsed().as_secs_f64(),
                stats.processed.separate_with_commas(),
                deque.len().separate_with_commas(),
                stats.steals_sent.separate_with_commas(),
                stats.work_received.separate_with_commas(),
            );
        }
        // 1. Service all pending messages.
        while let Some((message, status)) = world.any_process().immediate_matched_probe() {
            let source = status.source_rank();
            let tag = status.tag();
            let count = status.count(u8::equivalent_datatype()) as usize;
            let mut buf = vec![0u8; count];
            message.matched_receive_into(&mut buf[..]);
            match tag {
                TAG_STEAL => {
                    if deque.len() >= 2 && credit >= 2 {
                        let half = deque.len() / 2;
                        let continuations: Vec<Continuation> = deque.drain(..half).collect();
                        let give = credit / 2;
                        credit -= give;
                        let bytes = postcard::to_stdvec(&WorkMsg {
                            continuations,
                            credit: give,
                        })
                        .map_err(|e| internal(format!("work serialize: {e}")))?;
                        world
                            .process_at_rank(source)
                            .send_with_tag(&bytes[..], TAG_WORK);
                        stats.steals_served += 1;
                    } else {
                        world
                            .process_at_rank(source)
                            .send_with_tag(EMPTY, TAG_NOWORK);
                    }
                }
                TAG_WORK => {
                    let work: WorkMsg = postcard::from_bytes(&buf)
                        .map_err(|e| internal(format!("work deserialize: {e}")))?;
                    deque.extend(work.continuations);
                    credit += work.credit;
                    returned = false;
                    outstanding_steal = false;
                    stats.work_received += 1;
                }
                TAG_NOWORK => outstanding_steal = false,
                TAG_CREDIT => {
                    let mut bytes = [0u8; 8];
                    bytes.copy_from_slice(&buf[..8]);
                    home += u64::from_le_bytes(bytes);
                }
                TAG_STOP => {
                    invalid = buf.first() == Some(&1);
                    break 'run;
                }
                _ => {}
            }
        }

        // 2. Do one unit of work, if any.
        if let Some(cont) = deque.pop_front() {
            let (successors, terminal, local) = step_local(&ast, configuration, &cont)?;
            stats.processed += 1;
            total.union_with(local);
            if matches!(terminal, Some(Terminal::Invalid)) {
                for r in 0..size {
                    if r != rank {
                        world.process_at_rank(r).send_with_tag(&[1u8][..], TAG_STOP);
                    }
                }
                invalid = true;
                break 'run;
            }
            deque.extend(successors);
            continue;
        }

        // 3. Idle: return credit, detect global termination, then steal.
        stats.idle_iters += 1;
        if credit > 0 && !returned {
            if rank == 0 {
                home += credit;
            } else {
                world
                    .process_at_rank(0)
                    .send_with_tag(&credit.to_le_bytes()[..], TAG_CREDIT);
            }
            credit = 0;
            returned = true;
        }
        if rank == 0 && home == TOTAL_CREDIT {
            for r in 1..size {
                world.process_at_rank(r).send_with_tag(&[0u8][..], TAG_STOP);
            }
            break 'run;
        }
        if size > 1 && !outstanding_steal {
            let victim = lifelines[victim_idx % lifelines.len()];
            victim_idx += 1;
            world
                .process_at_rank(victim)
                .send_with_tag(EMPTY, TAG_STEAL);
            outstanding_steal = true;
            stats.steals_sent += 1;
        }
        // Yield the core while idle. On a real cluster (one rank per core) this
        // returns immediately, so stealing stays low-latency; when ranks share a
        // core (oversubscribed testing) it hands the core to a rank that has work,
        // so idle stealers do not starve the busy ones.
        std::thread::yield_now();
    }

    if invalid {
        return Ok(None);
    }
    stats.seconds = started.elapsed().as_secs_f64();

    // Reduce the disjoint per-rank accumulators by union (a collective; reached
    // by every rank only on a valid termination).
    let encoded =
        postcard::to_stdvec(&total).map_err(|e| internal(format!("accumulator serialize: {e}")))?;
    let buffers = all_gather_bytes(world, &encoded)?;
    let mut global = LocalAccumulators::default();
    for buffer in &buffers {
        let part: LocalAccumulators = postcard::from_bytes(buffer)
            .map_err(|e| internal(format!("accumulator deserialize: {e}")))?;
        global.union_with(part);
    }

    // Gather the per-rank utilisation the same way (every rank's stats, rank order).
    let encoded =
        postcard::to_stdvec(&stats).map_err(|e| internal(format!("stats serialize: {e}")))?;
    let buffers = all_gather_bytes(world, &encoded)?;
    let mut all_stats = Vec::with_capacity(buffers.len());
    for buffer in &buffers {
        all_stats.push(
            postcard::from_bytes::<RankStats>(buffer)
                .map_err(|e| internal(format!("stats deserialize: {e}")))?,
        );
    }

    Ok(Some((global, all_stats)))
}

/// A self-contained **benchmark / cluster test** for launching under `mpirun`:
/// it verifies the embedded program with the lifeline-work-stealing inner
/// backend ([`verify_configuration_mpi_stealing`]) and, on rank 0, **self-checks**
/// the distributed result against the single-process reference
/// ([`verify_configuration`]). Prints `OK` (and the wall-clock time + node count)
/// only when they match, so a wrapping test need only look for `OK`.
pub fn mpi_bench() {
    let universe = mpi::initialize().expect("MPI failed to initialise");
    let world = universe.world();
    let rank = world.rank();
    let size = world.size();

    let dialect = include_str!("../tests/hpc_demo/dialect.s").replace("\r\n", "\n");
    let chars: Vec<char> = dialect.chars().collect();
    let mut ast = crate::ast::new_ast(&chars, std::path::PathBuf::from("mpi-bench"));
    crate::compress(&mut ast);

    let systems = vec![
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 1,
        },
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 2,
        },
    ];

    let index = Ast::index(ast);
    let candidates = unsafe { candidate_configs(&index).expect("enumerate candidate configs") };
    let winner = unsafe { outer_sweep_winner(&world, ast, &systems, &candidates) }
        .expect("distributed outer sweep failed")
        .expect("the program has no valid configuration");
    let configuration = &candidates[winner];

    let start = std::time::Instant::now();
    let (distributed, _stats) =
        unsafe { verify_configuration_mpi_stealing(&world, ast, &systems, configuration, false) }
            .expect("distributed work-stealing verification failed")
            .expect("the winning configuration was rejected");
    let elapsed = start.elapsed();

    if rank == 0 {
        // Single-process reference for the same fixed configuration.
        let reference = match unsafe { verify_configuration(ast, &systems, configuration) }
            .expect("sequential reference failed")
        {
            ExplorePathResult::Valid(valid) => {
                unsafe { valid_path_to_local(ast, &valid) }.expect("re-key reference")
            }
            _ => unreachable!("reference rejected a configuration the sweep accepted"),
        };
        let status = if distributed == reference {
            "OK (matches single-process reference)"
        } else {
            "MISMATCH"
        };
        println!(
            "[mpi-bench] {size} rank(s); winning configuration = {} (candidate #{winner}); \
             work-stealing inner search took {:.3}s; touched {} node(s); accessed = {:?}; {status}",
            configuration,
            elapsed.as_secs_f64(),
            distributed.touched.len(),
            distributed.accessed,
        );
    }
}

/// Verify the program at `program_path` (a RISC-V dialect file, read relative to
/// the launch directory) under the lifeline work-stealing backend, emitting
/// **detailed live progress and a per-rank utilisation breakdown** to stdout -
/// the HPC counterpart a test pipes to a log file. `harts` lists the systems to
/// verify under (one per hart count, e.g. `[1, 2]`). Rank 0 prints a parseable
/// result line: `[mpi-verify] ranks=N program=P config=C touched=T accessed=A`.
pub fn mpi_verify(program_path: &str, harts: &[u8]) {
    let universe = mpi::initialize().expect("MPI failed to initialise");
    let world = universe.world();
    let rank = world.rank();
    let size = world.size();

    let source = std::fs::read_to_string(program_path)
        .unwrap_or_else(|e| panic!("mpi-verify: cannot read program `{program_path}`: {e}"));
    let dialect = source.replace("\r\n", "\n");
    let chars: Vec<char> = dialect.chars().collect();
    let mut ast = crate::ast::new_ast(&chars, std::path::PathBuf::from(program_path));
    crate::compress(&mut ast);

    let systems: Vec<InnerVerifierConfiguration> = harts
        .iter()
        .map(|&harts| InnerVerifierConfiguration {
            sections: Default::default(),
            harts,
        })
        .collect();

    let index = Ast::index(ast);
    let candidates = unsafe { candidate_configs(&index).expect("enumerate candidate configs") };
    if rank == 0 {
        println!(
            "[mpi-verify] starting: program={program_path} ranks={size} systems={harts:?} \
             candidate configurations={}",
            candidates.len(),
        );
    }

    let winner = unsafe { outer_sweep_winner(&world, ast, &systems, &candidates) }
        .expect("distributed outer sweep failed")
        .expect("the program has no valid configuration");
    let configuration = &candidates[winner];
    if rank == 0 {
        println!(
            "[mpi-verify] winning configuration = {configuration} (candidate #{winner}); \
             distributing the inner search across {size} rank(s)..."
        );
    }

    let (result, stats) =
        unsafe { verify_configuration_mpi_stealing(&world, ast, &systems, configuration, true) }
            .expect("distributed work-stealing verification failed")
            .expect("the winning configuration was rejected");

    if rank == 0 {
        // Per-rank utilisation table + a load-balance summary.
        println!("[utilisation] per-rank work-stealing breakdown:");
        println!("  rank  processed  steals_sent  steals_served  work_recv  idle_iters  seconds");
        let mut total_processed = 0u64;
        let (mut min_p, mut max_p) = (u64::MAX, 0u64);
        for s in &stats {
            total_processed += s.processed;
            min_p = min_p.min(s.processed);
            max_p = max_p.max(s.processed);
            println!(
                "  {:>4}  {:>11}  {:>11}  {:>13}  {:>9}  {:>11}  {:>7.3}",
                s.rank,
                s.processed.separate_with_commas(),
                s.steals_sent.separate_with_commas(),
                s.steals_served.separate_with_commas(),
                s.work_received.separate_with_commas(),
                s.idle_iters.separate_with_commas(),
                s.seconds,
            );
        }
        let balance = if min_p == 0 {
            f64::INFINITY
        } else {
            max_p as f64 / min_p as f64
        };
        let wall = stats.iter().map(|s| s.seconds).fold(0.0, f64::max);
        println!(
            "  total processed={} across {size} rank(s); \
             load balance max/min={balance:.2} (max {}, min {}); wall {wall:.3}s",
            total_processed.separate_with_commas(),
            max_p.separate_with_commas(),
            min_p.separate_with_commas(),
        );
        println!(
            "[mpi-verify] ranks={size} program={program_path} config={configuration} \
             touched={} accessed={:?}",
            result.touched.len(),
            result.accessed,
        );
    }
}

/// A self-contained distributed run for launching under `mpirun`: it verifies an
/// embedded program (`racy_store_inferred`) under a 1- and 2-hart system, using
/// **both** distributed axes - the outer sweep across ranks to infer the winning
/// configuration, then the inner frontier across ranks to verify it and reduce
/// its outputs. Rank 0 prints the inferred configuration and the runtime byte
/// ranges it accesses; both must match the sequential oracle (`value:Gu32`,
/// `value` bytes `0..4`), so a human or a wrapping test can confirm the
/// distributed run agrees with the single-process result.
pub fn mpi_selftest() {
    let universe = mpi::initialize().expect("MPI failed to initialise");
    let world = universe.world();
    let rank = world.rank();
    let size = world.size();

    let dialect = include_str!("../tests/racy_store_inferred/dialect.s").replace("\r\n", "\n");
    let chars: Vec<char> = dialect.chars().collect();
    let mut ast = crate::ast::new_ast(&chars, std::path::PathBuf::from("mpi-selftest"));
    crate::compress(&mut ast);

    let systems = vec![
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 1,
        },
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 2,
        },
    ];

    let index = Ast::index(ast);
    let candidates = unsafe { candidate_configs(&index).expect("enumerate candidate configs") };

    // Axis 1: distributed outer sweep -> the winning configuration index.
    let winner = unsafe { outer_sweep_winner(&world, ast, &systems, &candidates) }
        .expect("distributed outer sweep failed");

    let Some(winner) = winner else {
        if rank == 0 {
            println!(
                "[mpi-selftest] {size} rank(s): INVALID (no candidate configuration verified)"
            );
        }
        return;
    };

    // Axis 2: distributed inner verification of the winner, with continuation
    // migration across ranks, reducing the outputs.
    let outputs = unsafe { verify_configuration_mpi(&world, ast, &systems, &candidates[winner]) }
        .expect("distributed inner verification failed");

    if rank == 0 {
        match outputs {
            Some(accumulators) => {
                println!(
                    "[mpi-selftest] {size} rank(s): VALID; inferred configuration = {} \
                     (candidate #{winner}); touched {} node(s); accessed = {:?}",
                    candidates[winner],
                    accumulators.touched.len(),
                    accumulators.accessed,
                );
            }
            None => println!(
                "[mpi-selftest] {size} rank(s): inner verification returned Invalid (unexpected for the winner)"
            ),
        }
    }
}
