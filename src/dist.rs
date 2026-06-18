//! The distributed (MPI) backend, behind `--features hpc`.
//!
//! This is the real-transport counterpart of
//! [`crate::explore::verify_configuration_distributed_sim`]: where the
//! simulation hands continuation bytes between in-process "ranks", this
//! distributes work across actual MPI processes (`mpirun -n N`). It implements
//! the **outer configuration sweep** across ranks - the plan's primary
//! scale-out, and the one that needs almost no data movement: each rank verifies
//! the candidate configurations assigned to it (round-robin), and a single MPI
//! all-reduce selects the lowest-rank valid configuration (matching the
//! sequential oracle's "first valid in generator order" inference). Only a `u64`
//! index crosses the wire; the AST and the candidate list are derived
//! identically on every rank from the same program.
//!
//! Building this needs a system MPI library (rsmpi links it via `mpicc`); see
//! `build.rs`, which provisions it. Run it, for example, with:
//! `mpirun -n 24 target/debug/formal mpi-selftest`.

#![cfg(feature = "hpc")]

use crate::ast::Ast;
use crate::explore::{candidate_configs, verify_configuration};
use crate::verifier::{ExplorePathResult, InnerVerifierConfiguration};
use mpi::collective::SystemOperation;
use mpi::traits::*;

/// A real distributed verification across the MPI world, self-contained so it can
/// be launched directly under `mpirun`. It verifies a fixed embedded program
/// (`racy_store_inferred`) under a 1- and 2-hart system, distributing its
/// candidate configurations across the ranks and reducing to the inferred one.
/// Rank 0 prints the result; the inferred configuration must be `value:Gu32`,
/// exactly what the sequential oracle infers (so a human, or a wrapping test, can
/// confirm the distributed run agrees with the single-process result).
pub fn mpi_selftest() {
    let universe = mpi::initialize().expect("MPI failed to initialise");
    let world = universe.world();
    let rank = world.rank();
    let size = world.size();

    // The program is embedded and normalised to LF so it parses identically on
    // every rank regardless of the checkout's line endings.
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

    // Every rank enumerates the same candidate list in the same order.
    let index = Ast::index(ast);
    let candidates = unsafe { candidate_configs(&index).expect("enumerate candidate configs") };

    // Each rank verifies the candidates assigned to it (round-robin) and tracks
    // the lowest valid index it sees.
    let mut local_min: u64 = u64::MAX;
    let mut local_checked: u64 = 0;
    for (i, configuration) in candidates.iter().enumerate() {
        if i % (size as usize) == rank as usize {
            local_checked += 1;
            // SAFETY: `ast` heads this rank's live AST for the duration of the call.
            let outcome =
                unsafe { verify_configuration(ast, &systems, configuration) }.expect("verify");
            if matches!(outcome, ExplorePathResult::Valid(_)) {
                local_min = local_min.min(i as u64);
            }
        }
    }

    // Reduce: the global lowest valid index is the winning configuration; also
    // total how many candidates were checked, to show the work was spread.
    let mut winner: u64 = u64::MAX;
    let mut checked: u64 = 0;
    world.all_reduce_into(&local_min, &mut winner, SystemOperation::min());
    world.all_reduce_into(&local_checked, &mut checked, SystemOperation::sum());

    if rank == 0 {
        println!(
            "[mpi-selftest] {size} MPI rank(s) verified {} candidate configuration(s) \
             of racy_store_inferred ({checked} checks total)",
            candidates.len()
        );
        if winner == u64::MAX {
            println!("[mpi-selftest] result: INVALID (no candidate configuration verified)");
        } else {
            println!(
                "[mpi-selftest] result: VALID; inferred configuration = {} (candidate #{winner})",
                candidates[winner as usize]
            );
        }
    }
}
