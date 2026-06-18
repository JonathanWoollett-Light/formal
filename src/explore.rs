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

use crate::ast::AstNode;
use crate::verifier::{CompilerError, ExplorePathResult, Explorerer, InnerVerifierConfiguration};
use crate::verifier_types::TypeConfiguration;
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
