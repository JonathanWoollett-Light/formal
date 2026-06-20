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

/// `formal mpi-verify` built without the `hpc` feature reports the same
/// `hpc`-required message (a separate subcommand arm from `mpi-selftest`).
#[test]
fn mpi_verify_without_feature_errors() {
    let output = formal()
        .arg("mpi-verify")
        .output()
        .expect("run `formal mpi-verify`");
    assert!(
        !output.status.success(),
        "mpi-verify without `hpc` should fail"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("hpc"),
        "expected an `hpc`-feature hint"
    );
}

/// `formal new` with no project name prints the `new` usage and exits non-zero.
#[test]
fn new_without_name_prints_usage() {
    let output = formal().arg("new").output().expect("run `formal new`");
    assert!(
        !output.status.success(),
        "`formal new` with no name should fail"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("usage: formal new"),
        "expected the `new` usage text"
    );
}

/// When `cargo new` fails, `formal new` reports the error and exits non-zero
/// rather than panicking. Running it twice in the same directory makes the
/// second `cargo new` fail (the destination already exists), driving
/// `new_project`'s error path.
#[test]
fn new_into_existing_directory_fails() {
    let dir = std::env::temp_dir().join(format!("formal-cli-existing-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).expect("create temp dir");

    let first = formal()
        .args(["new", "demo"])
        .current_dir(&dir)
        .status()
        .expect("run `formal new demo`");
    assert!(
        first.success(),
        "the first `formal new demo` should succeed"
    );

    let second = formal()
        .args(["new", "demo"])
        .current_dir(&dir)
        .output()
        .expect("re-run `formal new demo`");
    assert!(
        !second.status.success(),
        "a second `formal new demo` (destination exists) should fail"
    );
    assert!(
        String::from_utf8_lossy(&second.stderr).contains("formal new:"),
        "expected the `formal new:` error prefix"
    );

    let _ = std::fs::remove_dir_all(&dir);
}
