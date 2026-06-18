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
use crate::explore::{candidate_configs, step_local, verify_configuration};
use crate::verifier::{
    Continuation, ExplorePathResult, InnerVerifierConfiguration, LocalAccumulators, Terminal,
};
use crate::verifier_types::{State, TypeConfiguration};
use mpi::collective::SystemOperation;
use mpi::datatype::PartitionMut;
use mpi::traits::*;
use mpi::Count;
use std::collections::BTreeMap;
use std::ptr::NonNull;

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
