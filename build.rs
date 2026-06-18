//! The project's single setup entry point.
//!
//! Cargo runs this before every (clean) build. It ensures the **system**
//! dependencies the test suite and the (planned) distributed backend need are
//! present: a WSL Linux environment on Windows, `qemu-system-riscv64` and a
//! RISC-V GNU toolchain for the QEMU boot tests, and a system MPI library for
//! the `--features hpc` distributed backend. The Rust crate dependencies
//! themselves are handled by Cargo as usual; this script only covers the things
//! Cargo cannot install.
//!
//! Design rules (so `cargo build` stays safe and predictable):
//! - **Never fails the build.** The library + default tests build with none of
//!   these present; missing system deps only disable the QEMU boots / `hpc`
//!   feature. Every probe/install error becomes a `cargo:warning`, never a panic.
//! - **Idempotent.** It re-detects each dependency and only acts on what is
//!   missing; when everything is present it prints nothing.
//! - **Non-interactive.** It only auto-installs via package managers without an
//!   elevation prompt (`sudo -n`, so it can't hang on a password). Anything that
//!   needs admin or a reboot (installing WSL itself, MS-MPI, a multi-GB
//!   toolchain) is reported as an exact command to run, not executed silently.
//! - **Controllable** via environment variables:
//!     - `FORMAL_NO_SETUP=1` - skip this script entirely.
//!     - `FORMAL_SETUP=detect` - detect and report only; never install.
//!     - `FORMAL_SETUP=install` - install even under CI (default is to detect
//!       only, not install, when `CI` is set).
//!   With none set, the default is detect + best-effort install (skipping the
//!   install step under `CI`/`DOCS_RS`).

use std::process::Command;

fn main() {
    // Only re-run when this script or its controls change, so it does not run on
    // every incremental build.
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=FORMAL_NO_SETUP");
    println!("cargo:rerun-if-env-changed=FORMAL_SETUP");
    println!("cargo:rerun-if-env-changed=RISCV_BIN");

    if std::env::var_os("FORMAL_NO_SETUP").is_some() {
        return;
    }

    let mode = std::env::var("FORMAL_SETUP").unwrap_or_default();
    let detect_only = mode == "detect" || std::env::var_os("DOCS_RS").is_some();
    let in_ci = std::env::var_os("CI").is_some();
    // Install by default; under CI only when explicitly asked.
    let install = !detect_only && (!in_ci || mode == "install");

    let mut report = Report::default();
    if cfg!(windows) {
        setup_windows(&mut report, install);
    } else {
        setup_unix(&mut report, install);
    }
    report.emit();
}

/// Accumulates human-facing lines; emitted as `cargo:warning=` so Cargo shows
/// them. Stays empty (and silent) when every dependency is already present.
#[derive(Default)]
struct Report {
    lines: Vec<String>,
}

impl Report {
    fn note(&mut self, line: impl Into<String>) {
        self.lines.push(line.into());
    }

    fn emit(&self) {
        if self.lines.is_empty() {
            return;
        }
        println!("cargo:warning=formal setup: some system dependencies are missing or were just installed");
        for line in &self.lines {
            println!("cargo:warning=  {line}");
        }
        println!(
            "cargo:warning=  (set FORMAL_NO_SETUP=1 to skip this, or FORMAL_SETUP=detect to only report)"
        );
    }
}

/// Whether `program` runs (exit status captured, not necessarily 0) - i.e. it
/// exists and is launchable. Errors (not found) return `false`.
fn runs(program: &str, args: &[&str]) -> bool {
    Command::new(program)
        .args(args)
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Whether `tool` is on the host PATH.
fn on_path(tool: &str) -> bool {
    if cfg!(windows) {
        runs("where", &[tool])
    } else {
        runs("sh", &["-c", &format!("command -v {tool}")])
    }
}

/// Run a best-effort, non-interactive install command, reporting the outcome.
/// `human` is the dependency name; `cmd`/`args` the installer invocation.
fn try_install(report: &mut Report, human: &str, cmd: &str, args: &[&str]) {
    match Command::new(cmd).args(args).output() {
        Ok(out) if out.status.success() => {
            report.note(format!("{human}: installed."));
        }
        Ok(_) => report.note(format!(
            "{human}: automatic install failed (needs elevation or a password?). Run manually:  {cmd} {}",
            args.join(" ")
        )),
        Err(e) => report.note(format!(
            "{human}: could not launch the installer ({e}). Run manually:  {cmd} {}",
            args.join(" ")
        )),
    }
}

/// Windows host: the QEMU boots and the toolchain live inside WSL (see
/// `tests/common/mod.rs`), so the work is to ensure WSL exists, then provision
/// the Linux side of it.
fn setup_windows(report: &mut Report, install: bool) {
    // WSL itself cannot be installed non-interactively (it needs admin + a
    // reboot), so only detect and instruct.
    let have_wsl = runs("wsl", &["--status"]) || on_path("wsl");
    if !have_wsl {
        report.note(
            "WSL is not installed. Install it (admin PowerShell, then reboot):  wsl --install",
        );
        report.note("after WSL is up, re-run `cargo build` to provision the Linux side.");
        // Native (non-WSL) MPI for the future `hpc` feature on Windows:
        report.note(
            "MPI (optional, for --features hpc): install Microsoft MPI, or use the MPI inside WSL.",
        );
        return;
    }

    // Provision the Linux side via apt, the same as a native Linux host.
    provision_linux(report, install, /* via_wsl = */ true);
}

/// Unix host (incl. inside WSL): detect and best-effort apt-install the deps.
fn setup_unix(report: &mut Report, install: bool) {
    provision_linux(report, install, /* via_wsl = */ false);
}

/// Detect + (optionally) install the Linux-side dependencies, either directly
/// (`via_wsl == false`) or by shelling into WSL (`via_wsl == true`).
fn provision_linux(report: &mut Report, install: bool, via_wsl: bool) {
    // A dependency is present iff its shell `probe` succeeds (run inside WSL, or
    // directly on a Unix host). The probe mirrors how the code actually finds the
    // tool, so an installed-but-not-on-PATH toolchain is not falsely flagged.
    let present = |probe: &str| {
        if via_wsl {
            runs("wsl", &["-e", "bash", "-lc", probe])
        } else {
            runs("sh", &["-c", probe])
        }
    };

    // The RISC-V toolchain default location used by `tests/common/mod.rs`
    // (`run_in_qemu` defaults `RISCV_BIN` to `$HOME/riscv-toolchain/riscv/bin`).
    let riscv_probe = "command -v riscv64-unknown-elf-as \
        || { [ -n \"$RISCV_BIN\" ] && [ -x \"$RISCV_BIN/riscv64-unknown-elf-as\" ]; } \
        || [ -x \"$HOME/riscv-toolchain/riscv/bin/riscv64-unknown-elf-as\" ]";

    // (presence probe, apt packages that provide it, human name).
    let deps: &[(&str, &str, &str)] = &[
        (
            "command -v qemu-system-riscv64",
            "qemu-system-misc",
            "QEMU (qemu-system-riscv64, for the bare-metal boot tests)",
        ),
        (
            riscv_probe,
            "gcc-riscv64-unknown-elf binutils-riscv64-unknown-elf",
            "RISC-V GNU toolchain (as/ld, for assembling the generated programs)",
        ),
        (
            "command -v mpicc",
            "libopenmpi-dev openmpi-bin",
            "system MPI (optional, for the --features hpc distributed backend)",
        ),
    ];

    let missing: Vec<&(&str, &str, &str)> = deps.iter().filter(|(p, _, _)| !present(p)).collect();
    if missing.is_empty() {
        return;
    }

    if !install {
        for (_, pkgs, human) in &missing {
            report.note(format!("{human}: missing. Install with:  sudo apt-get install -y {pkgs}"));
        }
        return;
    }

    // Best-effort, non-interactive apt install of everything missing in one go.
    let pkgs: Vec<&str> = missing
        .iter()
        .flat_map(|(_, p, _)| p.split(' '))
        .collect();
    let pkg_list = pkgs.join(" ");
    let apt = format!("sudo -n apt-get update && sudo -n DEBIAN_FRONTEND=noninteractive apt-get install -y {pkg_list}");

    if via_wsl {
        try_install(report, "WSL apt packages", "wsl", &["-e", "bash", "-lc", &apt]);
    } else {
        try_install(report, "apt packages", "sh", &["-c", &apt]);
    }

    // The toolchain the QEMU tests default to (`$HOME/riscv-toolchain/...`) is a
    // specific upstream release, not the apt package; if the boot tests still
    // cannot find it, point `RISCV_BIN` at whatever `as`/`ld` apt installed.
    report.note(
        "if a QEMU boot test reports a missing toolchain, set RISCV_BIN to the dir holding \
         riscv64-unknown-elf-as/ld (apt installs them on PATH; export RISCV_BIN accordingly).",
    );
}
