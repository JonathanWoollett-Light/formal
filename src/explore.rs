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

use crate::ast::{Ast, AstNode, Label};
use crate::verifier::{
    step, CompilerError, Continuation, ExplorePathResult, Explorerer, InnerVerifierConfiguration,
    RecordSinks, Terminal, ValidPathResult,
};
use crate::verifier_types::{AccessTransitions, AccessedRanges, State, TypeConfiguration};
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
        let outcome = step(&cont, &ast, configuration, &mut touched, &mut jumped, &mut sinks)?;
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
