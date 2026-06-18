//! Fixed-configuration verification: the **inner** search axis on its own.
//!
//! [`verify_configuration`] runs the verifier's inner exploration (hart
//! interleavings and the branch tree) for a single, pre-decided
//! [`TypeConfiguration`], with the **outer** type search removed. The
//! configuration is seeded up front, so [`Explorerer`]'s `load_label` validates
//! every `define`/`la`/`lat` against the already-set type and returns without
//! pulling a new candidate from a type iterator (see `load_label` in
//! [`crate::verifier`]); the exploration therefore never backtracks. A reachable
//! `#!` or a failed store/load check is simply `Invalid` *for this
//! configuration*.
//!
//! This is the sequential foundation the parallel/distributed backends build on:
//! the outer sweep (Phase 2) calls this once per candidate configuration, and
//! the in-process pool (Phase 1) replaces the body with a work-stealing loop over
//! pointer-free `Continuation`s that produces the identical union of outputs.

use crate::ast::{Ast, AstNode, AstNodeId, Instruction, Label, Type};
use crate::verifier::{
    locality_list, step, type_list, CompilerError, Continuation, ExplorePathResult, Explorerer,
    InnerVerifierConfiguration, LocalAccumulators, RecordSinks, Terminal, ValidPathResult,
};
use crate::verifier_types::{
    AccessTransitions, AccessedRanges, LabelLocality, State, TypeConfiguration,
};
use itertools::Itertools;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::ptr::NonNull;

/// Verifies the program at `ast`, run on `systems`, under the single fixed
/// `configuration`, returning the terminal [`ExplorePathResult`]: `Valid` with
/// the path result (the unioned outputs over every interleaving/branch of this
/// configuration), or `Invalid` if some path reaches a `#!` or a failed check.
///
/// Unlike the full [`Explorerer`] driver, this never explores an alternative
/// type assignment: the seeded `configuration` makes the inner search
/// self-contained, which is what lets the configurations be verified
/// independently (and, later, in parallel across cores and nodes).
///
/// # Safety
/// `ast` must head a live AST (see [`Explorerer::new`]) that outlives the call.
pub unsafe fn verify_configuration(
    ast: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
) -> Result<ExplorePathResult, CompilerError> {
    let mut explorerer = Explorerer::new(ast, systems)?;
    // Seed the configuration so the inner search never backtracks: with every
    // variable already present, `load_label` validates each definition against
    // it and returns without advancing a type iterator.
    explorerer.configuration = configuration.clone();
    loop {
        explorerer = match explorerer.next_step()? {
            ExplorePathResult::Continue(next) => next,
            terminal => return Ok(terminal),
        };
    }
}

/// A `Send`/`Sync` handle to the immutable, read-only AST so it can be shared
/// across the rayon worker threads of [`verify_sweep`]. This is sound because the
/// AST is never mutated during verification: each worker builds its own
/// `Explorerer` (and its own tree) and only *reads* the shared nodes.
#[derive(Clone, Copy)]
struct AstRef(Option<NonNull<AstNode>>);
// SAFETY: the pointee (the AST) is immutable for the lifetime of verification and
// only read concurrently; no worker mutates a shared node.
unsafe impl Send for AstRef {}
unsafe impl Sync for AstRef {}

impl AstRef {
    /// The wrapped AST head. Taking `self` by value means a closure that calls
    /// this captures the whole (`Send`/`Sync`) `AstRef`, not the inner
    /// `!Sync` `Option<NonNull<AstNode>>` field (2021 disjoint closure capture).
    fn ptr(self) -> Option<NonNull<AstNode>> {
        self.0
    }
}

/// The **outer configuration sweep**, run in parallel: verifies each candidate
/// configuration independently across a rayon work-stealing pool and returns the
/// best-ranked (lowest-index) `Valid` one, matching the sequential oracle's
/// "first valid in generator order" selection. If no candidate is valid the
/// program is `Invalid`.
///
/// Each candidate is an independent [`verify_configuration`] over the shared,
/// immutable AST, which is the whole point of the decoupling: the configurations
/// (and, with the pointer-free inner pool, a single configuration's frontier)
/// parallelise with no shared mutable state.
///
/// The parallel phase only computes *which* configurations are valid (the rank is
/// `Send`; the pointer-keyed `ValidPathResult` is not, pending the Phase-0d
/// re-key), then the winner's outputs are materialised with one more sequential
/// `verify_configuration`. That is a deliberate, documented double-verify of the
/// single winner, removed once the accumulators are re-keyed on [`AstNodeId`].
///
/// # Safety
/// `ast` must head a live AST that outlives the call (see [`Explorerer::new`]).
pub unsafe fn verify_sweep(
    ast: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    candidates: &[TypeConfiguration],
) -> Result<ExplorePathResult, CompilerError> {
    use rayon::prelude::*;

    let ast = AstRef(ast);
    // Verify candidates concurrently; keep only the ranks that are valid. The
    // `?`-bearing closure aborts the whole sweep on an internal compiler error.
    let valid_ranks = candidates
        .par_iter()
        .enumerate()
        .filter_map(move |(rank, configuration)| {
            // SAFETY: `ast` is read-only across threads (see `AstRef`).
            match unsafe { verify_configuration(ast.ptr(), systems, configuration) } {
                Ok(ExplorePathResult::Valid(_)) => Some(Ok(rank)),
                Ok(_) => None,
                Err(error) => Some(Err(error)),
            }
        })
        .collect::<Result<Vec<usize>, CompilerError>>()?;

    match valid_ranks.into_iter().min() {
        // Re-run the winner sequentially to obtain its (pointer-keyed) outputs.
        Some(rank) => verify_configuration(ast.ptr(), systems, &candidates[rank]),
        None => Ok(ExplorePathResult::Invalid),
    }
}

/// Fixed-configuration inner search over the pointer-free [`Continuation`]
/// frontier, the way the parallel pool will: seed one continuation per system,
/// drive [`step`] over an explicit worklist (no `*mut` tree), and union the
/// outputs. This is the sequential reference for the work-stealing pool to come;
/// it must produce the identical [`ValidPathResult`] as [`verify_configuration`]
/// for the same configuration (pinned by the cross-check test), which is what
/// proves `step` faithful before parallelising the worklist.
///
/// # Safety
/// `ast_head` must head a live AST that outlives the call.
pub unsafe fn verify_configuration_pooled(
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
) -> Result<ExplorePathResult, CompilerError> {
    let ast = Ast::index(ast_head);
    let start = ast.head().ok_or_else(|| {
        CompilerError::Internal("verify_configuration_pooled: empty AST".to_string())
    })?;
    let start_id = ast.id_of(start).ok_or_else(|| {
        CompilerError::Internal("verify_configuration_pooled: entry node not indexed".to_string())
    })?;

    // The shared, grow-only outputs (single-threaded: one set of sinks, exactly
    // like the global accumulators the sequential `Explorerer` keeps).
    let mut touched: BTreeSet<NonNull<AstNode>> = BTreeSet::new();
    let mut jumped: BTreeSet<NonNull<AstNode>> = BTreeSet::new();
    let mut accessed: AccessedRanges = AccessedRanges::new();
    let mut transitions: AccessTransitions = AccessTransitions::new();
    let mut uncompactable: BTreeSet<Label> = BTreeSet::new();
    let mut pinned_nodes: BTreeSet<NonNull<AstNode>> = BTreeSet::new();

    // Seed one continuation per system: every hart starts at the entry node,
    // hart 0 active (the analogue of `build_initial_chain`).
    let mut work: VecDeque<Continuation> = VecDeque::new();
    for system in systems {
        let state = State::new(system, configuration);
        let mut fronts = BTreeMap::new();
        for hart in 0..system.harts {
            fronts.insert(hart, start_id);
        }
        work.push_back(Continuation {
            state,
            fronts,
            active_hart: 0,
        });
    }

    // Drain the frontier. Any `Invalid` makes the whole configuration invalid
    // (no backtracking under a fixed configuration); a drained path just ends.
    while let Some(cont) = work.pop_front() {
        let mut sinks = RecordSinks {
            accessed: &mut accessed,
            transitions: &mut transitions,
            uncompactable: &mut uncompactable,
            pinned_nodes: &mut pinned_nodes,
        };
        let outcome = step(
            &cont,
            &ast,
            configuration,
            &mut touched,
            &mut jumped,
            &mut sinks,
        )?;
        if let Some(Terminal::Invalid) = outcome.terminal {
            return Ok(ExplorePathResult::Invalid);
        }
        work.extend(outcome.successors);
    }

    Ok(ExplorePathResult::Valid(ValidPathResult {
        configuration: configuration.clone(),
        touched,
        jumped,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    }))
}

/// Re-keys a set of pointer-keyed sinks onto the pointer-free [`AstNodeId`]
/// (Phase 0d), producing the `Send` [`LocalAccumulators`] the parallel pool
/// reduces. `accessed`/`uncompactable` are already `Label`-keyed, so only the
/// node-keyed sets/maps are translated through `ast`.
fn local_from_parts(
    ast: &Ast,
    touched: &BTreeSet<NonNull<AstNode>>,
    jumped: &BTreeSet<NonNull<AstNode>>,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned: &BTreeSet<NonNull<AstNode>>,
) -> Result<LocalAccumulators, CompilerError> {
    let id = |node: &NonNull<AstNode>| -> Result<AstNodeId, CompilerError> {
        ast.id_of(*node)
            .ok_or_else(|| CompilerError::Internal("re-key: node not in AST".to_string()))
    };
    let mut transitions_out: BTreeMap<AstNodeId, BTreeSet<(Label, u64, u64)>> = BTreeMap::new();
    for (node, ts) in transitions {
        transitions_out.insert(id(node)?, ts.clone());
    }
    Ok(LocalAccumulators {
        touched: touched.iter().map(id).collect::<Result<_, _>>()?,
        jumped: jumped.iter().map(id).collect::<Result<_, _>>()?,
        accessed: accessed.clone(),
        transitions: transitions_out,
        uncompactable: uncompactable.clone(),
        pinned_nodes: pinned.iter().map(id).collect::<Result<_, _>>()?,
    })
}

/// Re-keys a [`ValidPathResult`] (the pointer-keyed oracle/`verify_configuration`
/// output) onto [`AstNodeId`] so it can be compared against the parallel pool's
/// [`LocalAccumulators`]. This is the boundary the cross-check test uses.
///
/// # Safety
/// `ast_head` must head the same live AST the `ValidPathResult` was produced from.
pub unsafe fn valid_path_to_local(
    ast_head: Option<NonNull<AstNode>>,
    valid: &ValidPathResult,
) -> Result<LocalAccumulators, CompilerError> {
    let ast = Ast::index(ast_head);
    local_from_parts(
        &ast,
        &valid.touched,
        &valid.jumped,
        &valid.accessed,
        &valid.transitions,
        &valid.uncompactable,
        &valid.pinned_nodes,
    )
}

/// The **deep inner parallel** search: explore one fixed configuration's
/// frontier across a rayon work pool, the answer to "a single configuration must
/// still use many cores". Continuations are pointer-free and `Send`, so a whole
/// BFS wave of the frontier is stepped in parallel; each worker re-keys its
/// outputs onto [`AstNodeId`] (so they are `Send`) and they reduce by the
/// commutative union ([`LocalAccumulators::union_with`]). Returns `Some(union)`
/// if the configuration is valid (every path drained), or `None` if any path is
/// `Invalid` for it.
///
/// The union is order-independent, so the result is identical for any number of
/// worker threads or any scheduling (pinned by the cross-check test). This is the
/// wave-synchronised form; the work-stealing pool (and the distributed layer) are
/// the same continuation unit with a finer scheduler.
///
/// # Safety
/// The AST `ast` indexes must be live and outlive the call. Build it once with
/// [`Ast::index`] and share `&Ast` (it is `Send`/`Sync`) across the pool.
pub unsafe fn verify_configuration_parallel(
    ast: &Ast,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
) -> Result<Option<LocalAccumulators>, CompilerError> {
    use rayon::prelude::*;

    let start = ast.head().ok_or_else(|| {
        CompilerError::Internal("verify_configuration_parallel: empty AST".to_string())
    })?;
    let start_id = ast.id_of(start).ok_or_else(|| {
        CompilerError::Internal("verify_configuration_parallel: entry node not indexed".to_string())
    })?;

    // Seed: one continuation per system, all harts at the entry, hart 0 active.
    let mut frontier: Vec<Continuation> = systems
        .iter()
        .map(|system| {
            let state = State::new(system, configuration);
            let mut fronts = BTreeMap::new();
            for hart in 0..system.harts {
                fronts.insert(hart, start_id);
            }
            Continuation {
                state,
                fronts,
                active_hart: 0,
            }
        })
        .collect();

    let mut total = LocalAccumulators::default();

    // Process the frontier wave by wave; each wave is stepped in parallel.
    while !frontier.is_empty() {
        type WaveItem = (Vec<Continuation>, Option<Terminal>, LocalAccumulators);
        let wave = frontier
            .par_iter()
            .map(|cont| -> Result<WaveItem, CompilerError> {
                let mut touched = BTreeSet::new();
                let mut jumped = BTreeSet::new();
                let mut accessed = AccessedRanges::new();
                let mut transitions = AccessTransitions::new();
                let mut uncompactable = BTreeSet::new();
                let mut pinned = BTreeSet::new();
                let outcome = {
                    let mut sinks = RecordSinks {
                        accessed: &mut accessed,
                        transitions: &mut transitions,
                        uncompactable: &mut uncompactable,
                        pinned_nodes: &mut pinned,
                    };
                    // SAFETY: `ast` is read-only and shared across workers; `cont`
                    // references its nodes.
                    unsafe {
                        step(
                            cont,
                            ast,
                            configuration,
                            &mut touched,
                            &mut jumped,
                            &mut sinks,
                        )?
                    }
                };
                let local = local_from_parts(
                    ast,
                    &touched,
                    &jumped,
                    &accessed,
                    &transitions,
                    &uncompactable,
                    &pinned,
                )?;
                Ok((outcome.successors, outcome.terminal, local))
            })
            .collect::<Result<Vec<WaveItem>, CompilerError>>()?;

        let mut next = Vec::new();
        for (successors, terminal, local) in wave {
            if let Some(Terminal::Invalid) = terminal {
                return Ok(None);
            }
            total.union_with(local);
            next.extend(successors);
        }
        frontier = next;
    }

    Ok(Some(total))
}

/// Enumerate candidate configurations for the program's variables, in the order
/// the sequential explorer prefers (`locality_list` x `type_list` per variable,
/// locality outer), so the parallel sweep's lowest-rank valid match is the
/// configuration the oracle would infer. Every variable referenced by a
/// `define`/`la`/`lat` gets the full locality x type product; an annotation is
/// not special-cased here, it simply makes all but the annotated assignment
/// invalid during verification.
///
/// The product is `(2 x 8)^v` for `v` variables, fine for the small `v` of real
/// programs; large `v` wants lazy generation and branch-and-bound pruning
/// (future work, noted in the plan).
///
/// # Safety
/// `ast` must index a live AST.
pub unsafe fn candidate_configs(ast: &Ast) -> Result<Vec<TypeConfiguration>, CompilerError> {
    // Variables the program references, deduplicated and ordered by label.
    let mut labels: BTreeSet<Label> = BTreeSet::new();
    for i in 0..ast.len() {
        let node = ast.resolve(AstNodeId(i as u32)).ok_or_else(|| {
            CompilerError::Internal("candidate_configs: index out of range".to_string())
        })?;
        match &node.as_ref().as_ref().this {
            Instruction::Define(define) => {
                labels.insert(define.label.clone());
            }
            Instruction::La(la) => {
                labels.insert(la.label.clone());
            }
            Instruction::Lat(lat) => {
                labels.insert(lat.label.clone());
            }
            _ => {}
        }
    }

    // A program with no variables verifies under the single empty configuration.
    if labels.is_empty() {
        return Ok(vec![TypeConfiguration::new()]);
    }

    // Per-variable options in `locality_list` x `type_list` order (the explorer's
    // `load_label` enumeration order).
    let options: Vec<(LabelLocality, Type)> = locality_list()
        .into_iter()
        .flat_map(|locality| {
            type_list()
                .into_iter()
                .map(move |ty| (LabelLocality::from(locality), ty))
        })
        .collect();

    Ok(labels
        .iter()
        .map(|label| options.iter().map(move |opt| (label.clone(), opt.clone())))
        .multi_cartesian_product()
        .map(|assignment| TypeConfiguration(assignment.into_iter().collect()))
        .collect())
}

/// End-to-end **inferred** verification: enumerate candidate configurations
/// ([`candidate_configs`]) and run the parallel outer sweep ([`verify_sweep`]),
/// returning the best-ranked valid configuration (the one the oracle would infer)
/// or `Invalid`. This closes the outer axis: the caller supplies only the AST and
/// systems, no hand-written candidate list.
///
/// # Safety
/// `ast_head` must head a live AST that outlives the call.
pub unsafe fn verify_inferred(
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
) -> Result<ExplorePathResult, CompilerError> {
    let ast = Ast::index(ast_head);
    let candidates = candidate_configs(&ast)?;
    verify_sweep(ast_head, systems, &candidates)
}

/// Distributed-transport **simulation** of the deep inner search: identical to
/// [`verify_configuration_parallel`], except every frontier item crosses a
/// `postcard` serialize -> deserialize round-trip before it is stepped and every
/// successor is re-serialized, exactly as a `Continuation` would when migrating
/// between cluster nodes. The per-worker outputs reduce by the same commutative
/// union. This exercises the real interop boundary (serde + a compact binary
/// format) and proves continuations survive the wire with byte-identical results;
/// the only thing a real MPI/lifeline backend swaps in is the *transport* of
/// these bytes (validated on a cluster, not here).
///
/// Returns `Some(union)` if the configuration is valid, or `None` if invalid.
///
/// # Safety
/// The AST `ast` indexes must be live and outlive the call.
pub unsafe fn verify_configuration_distributed_sim(
    ast: &Ast,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
) -> Result<Option<LocalAccumulators>, CompilerError> {
    use rayon::prelude::*;

    let encode = |cont: &Continuation| -> Result<Vec<u8>, CompilerError> {
        postcard::to_stdvec(cont)
            .map_err(|e| CompilerError::Internal(format!("continuation serialize: {e}")))
    };
    let decode = |bytes: &[u8]| -> Result<Continuation, CompilerError> {
        postcard::from_bytes(bytes)
            .map_err(|e| CompilerError::Internal(format!("continuation deserialize: {e}")))
    };

    let start = ast.head().ok_or_else(|| {
        CompilerError::Internal("verify_configuration_distributed_sim: empty AST".to_string())
    })?;
    let start_id = ast.id_of(start).ok_or_else(|| {
        CompilerError::Internal(
            "verify_configuration_distributed_sim: entry not indexed".to_string(),
        )
    })?;

    // The frontier is carried as serialized bytes, as if in transit between nodes.
    let mut frontier: Vec<Vec<u8>> = systems
        .iter()
        .map(|system| {
            let mut fronts = BTreeMap::new();
            for hart in 0..system.harts {
                fronts.insert(hart, start_id);
            }
            encode(&Continuation {
                state: State::new(system, configuration),
                fronts,
                active_hart: 0,
            })
        })
        .collect::<Result<_, _>>()?;

    let mut total = LocalAccumulators::default();

    while !frontier.is_empty() {
        type WaveItem = (Vec<Vec<u8>>, Option<Terminal>, LocalAccumulators);
        let wave = frontier
            .par_iter()
            .map(|bytes| -> Result<WaveItem, CompilerError> {
                // Receive: deserialize the migrated continuation.
                let cont = decode(bytes)?;

                let mut touched = BTreeSet::new();
                let mut jumped = BTreeSet::new();
                let mut accessed = AccessedRanges::new();
                let mut transitions = AccessTransitions::new();
                let mut uncompactable = BTreeSet::new();
                let mut pinned = BTreeSet::new();
                let outcome = {
                    let mut sinks = RecordSinks {
                        accessed: &mut accessed,
                        transitions: &mut transitions,
                        uncompactable: &mut uncompactable,
                        pinned_nodes: &mut pinned,
                    };
                    // SAFETY: `ast` is read-only and shared; `cont` references its nodes.
                    unsafe {
                        step(
                            &cont,
                            ast,
                            configuration,
                            &mut touched,
                            &mut jumped,
                            &mut sinks,
                        )?
                    }
                };
                let local = local_from_parts(
                    ast,
                    &touched,
                    &jumped,
                    &accessed,
                    &transitions,
                    &uncompactable,
                    &pinned,
                )?;
                // Send: re-serialize the successors for the next hop.
                let successors = outcome
                    .successors
                    .iter()
                    .map(&encode)
                    .collect::<Result<Vec<_>, _>>()?;
                Ok((successors, outcome.terminal, local))
            })
            .collect::<Result<Vec<WaveItem>, CompilerError>>()?;

        let mut next = Vec::new();
        for (successors, terminal, local) in wave {
            if let Some(Terminal::Invalid) = terminal {
                return Ok(None);
            }
            total.union_with(local);
            next.extend(successors);
        }
        frontier = next;
    }

    Ok(Some(total))
}
