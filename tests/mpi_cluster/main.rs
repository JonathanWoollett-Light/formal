//! Cluster-scale execution test: run the distributed verifier under `mpirun`
//! across many processes (each process simulates a cluster node) and assert it
//! agrees with the sequential oracle.
//!
//! This builds the `--features hpc` binary in WSL (where the system MPI library
//! lives) and launches it with `mpirun -n N`, for several `N`, simulating a
//! 1-, 4-, and 24-"node" cluster. It exercises both distributed axes end to end:
//! the outer configuration sweep across ranks, and the inner frontier migrated
//! across ranks (continuations serialised and MPI-exchanged), reduced to the
//! inferred configuration and accessed byte-ranges.
//!
//! `#[ignore]`d because it is heavy (a WSL `--features hpc` build + `mpirun`) and
//! environment-specific (needs WSL + a system MPI). Run it explicitly:
//!   cargo nt --run-ignored all -E 'binary(mpi_cluster)'
//! Like the QEMU boot tests, it *fails* (not skips) if WSL / MPI are absent: the
//! point is to actually run the cluster.

use std::process::Command;

/// Build the `--features hpc` binary in WSL (idempotent; cached after the first
/// call) and run `formal <subcommand>` under `mpirun -n ranks`, returning the
/// merged stdout (only rank 0 prints the result line).
fn mpirun(ranks: usize, subcommand: &str) -> String {
    // One WSL bash session: locate the repo via `wslpath`, build (quietly, with
    // setup skipped so build.rs does not interfere), then launch under mpirun.
    let dir = env!("CARGO_MANIFEST_DIR");
    let script = format!(
        "set -e\n\
         cd \"$(wslpath '{dir}')\"\n\
         FORMAL_NO_SETUP=1 ~/.cargo/bin/cargo build --features hpc --bin formal \
            --target-dir ~/formal-hpc >/dev/null 2>&1\n\
         mpirun --oversubscribe -n {ranks} ~/formal-hpc/debug/formal {subcommand}"
    );

    let mut command = Command::new("wsl");
    command.args(["-e", "bash", "-lc", &script]);
    // Detach WSL from the console (as `run_in_qemu` does) so it does not corrupt
    // the test runner's display.
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        const CREATE_NO_WINDOW: u32 = 0x0800_0000;
        command.creation_flags(CREATE_NO_WINDOW);
    }

    let output = command.output().expect(
        "failed to invoke WSL: WSL with a system MPI (mpirun) and the `--features hpc` build \
         deps is required to run the distributed cluster test",
    );
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "wsl build/mpirun failed for {ranks} rank(s):\n--- stdout ---\n{stdout}\n--- stderr ---\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// Under `mpirun` at 1, 4, and 24 ranks, the distributed verifier infers
/// `racy_store_inferred`'s configuration (`value:Gu32`) and its runtime accessed
/// byte-range (`value` bytes `0..4`) - identical at every rank count, and
/// identical to what the single-process oracle infers (pinned in
/// `tests/racy_store_inferred`).
#[test]
#[ignore = "heavy: builds --features hpc in WSL and runs under mpirun; run with --run-ignored all"]
fn distributed_verification_matches_oracle_across_ranks() {
    for ranks in [1usize, 4, 24] {
        let out = mpirun(ranks, "mpi-selftest");
        assert!(
            out.contains("VALID"),
            "ranks={ranks}: expected a valid result, got:\n{out}"
        );
        assert!(
            out.contains("value:Gu32"),
            "ranks={ranks}: expected the inferred configuration value:Gu32, got:\n{out}"
        );
        // The dead-data-elimination output: the program accesses exactly the four
        // bytes of `value: u32` at runtime.
        assert!(
            out.contains("\"value\": {(0, 4)}"),
            "ranks={ranks}: expected accessed = value bytes 0..4, got:\n{out}"
        );
    }
}

/// The **load-balanced** path on a **relatively large** program: under `mpirun`
/// at 8, 16, and 24 ranks (a simulated multi-node cluster), the lifeline
/// work-stealing inner backend ([`verify_configuration_mpi_stealing`]) verifies
/// the embedded `hpc_demo` program (a racy interleaving search with a frontier in
/// the hundreds of thousands of continuations) and **self-checks** its result against
/// the single-process reference. `mpi-bench` prints `OK` only on a match, so the
/// test confirms the steal/migrate/terminate protocol produces the reference
/// result at every cluster size. Runs comfortably under a minute per rank count.
#[test]
#[ignore = "heavy: builds --features hpc in WSL and runs under mpirun; run with --run-ignored all"]
fn work_stealing_cluster_matches_reference_on_large_program() {
    for ranks in [8usize, 16, 24] {
        let out = mpirun(ranks, "mpi-bench");
        assert!(
            out.contains("OK (matches single-process reference)"),
            "ranks={ranks}: distributed work-stealing result did not match the reference:\n{out}"
        );
    }
}
