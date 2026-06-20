//! Covers the `formal` command-line tool ([`src/main.rs`](../../src/main.rs)) by
//! running the built binary: scaffolding a project, the no-argument usage text,
//! and the feature-gated `mpi-*` subcommands' error when built without `hpc`.
//! These are sensible end-user behaviours (does the CLI work), and running the
//! binary is what attributes coverage to `main.rs`.

use std::process::Command;

/// The `formal` binary built for this test run (Cargo sets `CARGO_BIN_EXE_formal`).
fn formal() -> Command {
    Command::new(env!("CARGO_BIN_EXE_formal"))
}

/// `formal new <name>` scaffolds a runnable project: a `main.hl`, the build-script
/// `src/main.rs`, and a `Cargo.toml` depending on `formal`.
#[test]
fn new_scaffolds_a_project() {
    let dir = std::env::temp_dir().join(format!("formal-cli-new-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create temp dir");

    let status = formal()
        .args(["new", "demo"])
        .current_dir(&dir)
        .status()
        .expect("run `formal new demo`");
    assert!(status.success(), "`formal new` exited non-zero");

    assert!(dir.join("demo/main.hl").is_file(), "main.hl scaffolded");
    assert!(
        dir.join("demo/src/main.rs").is_file(),
        "build script scaffolded"
    );
    let manifest =
        std::fs::read_to_string(dir.join("demo/Cargo.toml")).expect("read scaffolded Cargo.toml");
    assert!(
        manifest.contains("formal"),
        "scaffolded Cargo.toml depends on `formal`"
    );

    let _ = std::fs::remove_dir_all(&dir);
}

/// With no arguments the CLI prints usage and exits non-zero.
#[test]
fn no_args_prints_usage() {
    let output = formal().output().expect("run `formal`");
    assert!(!output.status.success(), "no-arg invocation should fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("usage"),
        "expected usage text, got: {stderr}"
    );
}

/// `formal mpi-selftest` built without the `hpc` feature reports that the feature
/// (and a system MPI) is required, rather than crashing.
#[test]
fn mpi_subcommand_without_feature_errors() {
    let output = formal()
        .arg("mpi-selftest")
        .output()
        .expect("run `formal mpi-selftest`");
    assert!(
        !output.status.success(),
        "mpi-selftest without `hpc` should fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("hpc"),
        "expected an `hpc`-feature hint, got: {stderr}"
    );
}
