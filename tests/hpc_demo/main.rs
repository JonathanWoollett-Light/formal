//! Demonstrates the **HPC (distributed MPI) model** verifying a program much
//! larger than "Hello World!": `racy_stress`, a racy interleaving search whose
//! frontier runs to hundreds of thousands of continuations.
//!
//! Run it directly with:
//!
//! ```text
//! cargo nt hpc_demo
//! ```
//!
//! It uses the reusable [`verify_with_model`] helper, so the same test can be
//! flipped to the simple in-process model **without an edit**, before running:
//!
//! ```text
//! FORMAL_TEST_MODEL=sequential cargo nt hpc_demo   # in-process instead of MPI
//! FORMAL_TEST_MODEL=hpc:16     cargo nt hpc_demo   # 16 ranks instead of 8
//! ```
//!
//! In the HPC model the run streams per-rank live progress and a utilisation
//! breakdown (steps processed, steals, idle, load balance) to
//! `target/tmp/test-logs/<test>/hpc.log`; the assertion below confirms the
//! distributed result is the one the oracle infers (`value:Gu32`, accessing
//! `value`'s 4 bytes).
//!
//! Like the QEMU boot tests, this is **not** `#[ignore]`d and *fails* (does not
//! skip) if WSL / a system MPI are absent: it builds `--features hpc` in WSL and
//! launches `mpirun`.

#[path = "../common/mod.rs"]
mod common;

use common::*;

#[test]
fn hpc_demo() {
    // 8 MPI ranks (simulated nodes); 1- and 2-hart systems.
    let outcome = verify_with_model("racy_stress/dialect.s", &[1, 2], Model::Hpc { ranks: 8 });

    // Surfaced on failure (nextest captures per-test stderr); the full per-rank
    // progress + utilisation log is at `outcome.log`.
    eprintln!(
        "[{}] configuration={} touched={} accessed={}  (detail log: {})",
        outcome.model, outcome.configuration, outcome.touched, outcome.accessed, outcome.log,
    );

    // The distributed run must infer exactly what the single-process oracle does.
    assert!(
        outcome.configuration.contains("value:Gu32"),
        "unexpected configuration {} (see {})",
        outcome.configuration,
        outcome.log,
    );
    assert!(
        outcome.accessed.contains("\"value\": {(0, 4)}"),
        "unexpected accessed ranges {} (see {})",
        outcome.accessed,
        outcome.log,
    );
}
