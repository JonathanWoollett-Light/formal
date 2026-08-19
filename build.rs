//! The project's single setup entry point.
//!
//! Cargo runs this before every (clean) build. It ensures the **system**
//! dependencies the test suite and the (planned) distributed backend need are
//! present: a WSL Linux environment on Windows, `qemu-system-riscv64`, the
//! user-mode `qemu-riscv64` and a RISC-V GNU toolchain for the QEMU tests, and
//! a system MPI library for the `--features hpc` distributed backend. The Rust
//! crate dependencies themselves are handled by Cargo as usual; this script
//! only covers the things Cargo cannot install.
//!
//! Design rules (so `cargo build` stays safe and predictable):
//! - **Never fails the build.** The library + default tests build with none of
//!   these present; missing system deps only disable the QEMU boots / `hpc`
//!   feature. Every probe/install error becomes a `cargo:warning`, never a panic.
//! - **Idempotent.** It re-detects each dependency and only acts on what is
//!   missing; when everything is present it prints nothing. This is also what
//!   makes the reboot/resume flow work: the re-run after a reboot simply
//!   continues with whatever is still missing.
//! - **Escalates where genuinely required.** On Windows the QEMU / RISC-V
//!   toolchain / MPI packages install *inside WSL as root* (`wsl -u root`), which
//!   is privileged in the distribution without any UAC prompt or WSL password.
//!   Installing WSL itself needs host admin: `wsl --install` is tried directly
//!   first (an admin token - an admin terminal, or any Windows OpenSSH session
//!   of an admin user - needs no ceremony), with a UAC elevation request
//!   (`Start-Process -Verb RunAs`) as the fallback, judged by the resulting
//!   feature state rather than exit codes. On a native Linux host the apt install uses
//!   `sudo`, which prompts for your password on the terminal; with no console
//!   but an explicit `FORMAL_SETUP=install` (the CI opt-in) it uses `sudo -n`,
//!   which never prompts and so either works (passwordless sudo, the standard
//!   CI setup) or fails fast. A multi-GB upstream toolchain release is still
//!   reported, not downloaded silently.
//! - **Handles reboots.** When a step needs a reboot to finish (installing WSL
//!   itself; an apt install that newly leaves `/var/run/reboot-required`), it
//!   asks `[y/N]` on the console. On `y` it first schedules `cargo build` to
//!   re-run at the next login (an `HKCU` RunOnce entry on Windows; a
//!   self-removing login-shell hook on Linux that expires after two weeks if
//!   it never fires) and then reboots, so setup continues where it left off;
//!   any other answer reports what to do manually.
//! - **Interactive only where a human is present.** Prompts (sudo, the reboot
//!   question) go straight to the console device (`/dev/tty` on Unix, `CONIN$`
//!   on Windows) because Cargo captures build-script output and nulls its
//!   stdin. With no console attached, with the build not in the terminal's
//!   foreground (a backgrounded `cargo build &` reading /dev/tty would be
//!   stopped by SIGTTIN), or in a recognized CI environment (`CI`,
//!   `JENKINS_URL`, `TF_BUILD`, ...), nothing prompts and the report instructs
//!   instead.
//! - **Controllable** via environment variables:
//!     - `FORMAL_NO_SETUP=1` - skip this script entirely.
//!     - `FORMAL_SETUP=detect` - detect and report only; never install.
//!     - `FORMAL_SETUP=install` - install even under CI (default is to detect
//!       only, not install, when `CI` is set).
//!
//!   With none set, the default is detect + best-effort install (skipping the
//!   install step under `CI`/`DOCS_RS`).

use std::fs;
use std::path::Path;
use std::process::Command;

fn main() {
    // Only re-run when this script or its controls change, so it does not run on
    // every incremental build. (The post-reboot resume relies on this too: the
    // resume runs with FORMAL_SETUP=install, and that env change is what forces
    // this script to re-run even though nothing else changed.)
    println!("cargo:rerun-if-changed=build.rs");
    println!("cargo:rerun-if-env-changed=FORMAL_NO_SETUP");
    println!("cargo:rerun-if-env-changed=FORMAL_SETUP");
    println!("cargo:rerun-if-env-changed=RISCV_BIN");

    if std::env::var_os("FORMAL_NO_SETUP").is_some() {
        return;
    }

    let mode = std::env::var("FORMAL_SETUP").unwrap_or_default();
    let detect_only = mode == "detect" || std::env::var_os("DOCS_RS").is_some();
    let in_ci = in_ci();
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

/// Run a best-effort install command, reporting the outcome; returns whether it
/// succeeded. `human` is the dependency name; `cmd`/`args` the installer.
fn try_install(report: &mut Report, human: &str, cmd: &str, args: &[&str]) -> bool {
    match Command::new(cmd).args(args).output() {
        Ok(out) if out.status.success() => {
            report.note(format!("{human}: installed."));
            true
        }
        Ok(_) => {
            report.note(format!(
                "{human}: automatic install failed (needs elevation or a password?). Run manually:  {cmd} {}",
                args.join(" ")
            ));
            false
        }
        Err(e) => {
            report.note(format!(
                "{human}: could not launch the installer ({e}). Run manually:  {cmd} {}",
                args.join(" ")
            ));
            false
        }
    }
}

/// Whether this looks like a CI environment. Most systems set `CI`, but
/// Jenkins, Azure DevOps and TeamCity do not, and prompting (or sudo-ing) an
/// unattended agent must never happen.
fn in_ci() -> bool {
    [
        "CI",
        "GITHUB_ACTIONS",
        "GITLAB_CI",
        "CIRCLECI",
        "TRAVIS",
        "BUILDKITE",
        "TF_BUILD",
        "JENKINS_URL",
        "TEAMCITY_VERSION",
    ]
    .iter()
    .any(|v| std::env::var_os(v).is_some())
}

/// Open the real console for interactive prompts: `/dev/tty` on Unix,
/// `CONIN$`/`CONOUT$` on Windows. Cargo captures build-script stdout/stderr
/// (and nulls stdin), so the std streams are useless for prompting; the
/// console device bypasses that (it is how sudo prompts, too). `None` when no
/// console is attached (GUI-spawned builds), when the build does not own the
/// terminal's foreground (a backgrounded `cargo build &` reading /dev/tty
/// would be stopped by SIGTTIN), or on CI (never block a pipeline on a
/// prompt).
fn console() -> Option<(fs::File, fs::File)> {
    if in_ci() {
        return None;
    }
    let (in_dev, out_dev) = if cfg!(windows) {
        ("CONIN$", "CONOUT$")
    } else {
        ("/dev/tty", "/dev/tty")
    };
    // CONIN$ wants GENERIC_READ|GENERIC_WRITE; harmless on /dev/tty.
    let input = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .open(in_dev)
        .ok()?;
    if !tty_is_foreground(&input) {
        return None;
    }
    let output = fs::OpenOptions::new().write(true).open(out_dev).ok()?;
    Some((input, output))
}

/// Unix: whether this build owns the foreground of its controlling terminal.
/// Reading /dev/tty from a background process group raises SIGTTIN, which
/// stops the whole job; treat background as "no console" instead.
#[cfg(unix)]
fn tty_is_foreground(tty: &fs::File) -> bool {
    use std::os::unix::io::AsRawFd;
    // SAFETY: plain queries on a valid open fd / the current process.
    unsafe { libc::tcgetpgrp(tty.as_raw_fd()) == libc::getpgrp() }
}

/// Windows: no SIGTTIN equivalent; an attached console is enough.
#[cfg(windows)]
fn tty_is_foreground(_tty: &fs::File) -> bool {
    true
}

/// Ask a yes/no question on the console; `y`/`Y` means yes, anything else
/// (including just Enter) means no. `None` when there is no console to ask on.
fn prompt_yes(question: &str) -> Option<bool> {
    use std::io::{BufRead, BufReader, Write};
    let (input, mut output) = console()?;
    write!(output, "\n{question} [y/N] ").ok()?;
    output.flush().ok()?;
    let mut line = String::new();
    BufReader::new(input).read_line(&mut line).ok()?;
    Some(line.trim().eq_ignore_ascii_case("y"))
}

/// The two ingredients of the post-reboot resume command: this repository and
/// the cargo binary running the current build.
fn resume_ingredients() -> (String, String) {
    let repo = std::env::var("CARGO_MANIFEST_DIR").unwrap_or_else(|_| ".".into());
    let cargo = std::env::var("CARGO").unwrap_or_else(|_| "cargo".into());
    (repo, cargo)
}

/// Windows: schedule `cargo build` to re-run once at the next login, via a
/// batch file in `%TEMP%` registered under the current user's `RunOnce` key
/// (Windows deletes the registry value after running it; the batch file
/// deletes itself when done).
fn schedule_resume_windows() -> Result<String, String> {
    let (repo, cargo) = resume_ingredients();
    // `%` is the one character cmd.exe still expands inside double quotes in a
    // batch file; double it so paths containing it stay literal.
    let (repo, cargo) = (repo.replace('%', "%%"), cargo.replace('%', "%%"));
    let bat = std::env::temp_dir().join("formal-setup-resume.cmd");
    // CRLF line endings: cmd.exe mis-parses some constructs (goto scanning) in
    // LF-only batch files. And the file is written as UTF-8 while a fresh
    // RunOnce console starts at the OEM codepage, so switch the codepage first
    // or non-ASCII paths (C:\Users\José\...) are mojibake'd.
    let script = [
        "@echo off",
        "chcp 65001 >nul",
        "title formal setup (resuming after reboot)",
        &format!("cd /d \"{repo}\""),
        "set \"FORMAL_SETUP=install\"",
        &format!("\"{cargo}\" build"),
        "echo.",
        "echo formal setup: resumed build finished. Press any key to close.",
        "pause >nul",
        "(goto) 2>nul & del \"%~f0\"",
        "",
    ]
    .join("\r\n");
    fs::write(&bat, script).map_err(|e| format!("writing {}: {e}", bat.display()))?;
    let value = format!("cmd /c start \"formal setup\" \"{}\"", bat.display());
    let out = Command::new("reg")
        .args([
            "add",
            r"HKCU\Software\Microsoft\Windows\CurrentVersion\RunOnce",
            "/v",
            "formal-setup-resume",
            "/t",
            "REG_SZ",
            "/d",
            &value,
            "/f",
        ])
        .output()
        .map_err(|e| format!("launching reg.exe: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "reg.exe add failed: {}",
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    Ok("`cargo build` is scheduled (RunOnce) to re-run when you next log in".to_string())
}

/// Shell-single-quote `s` so it stays one inert word in generated sh code (a
/// path containing `$`, backticks, spaces or quotes must neither expand nor
/// split, let alone execute).
fn sh_quote(s: &str) -> String {
    format!("'{}'", s.replace('\'', r"'\''"))
}

/// Linux: schedule `cargo build` to re-run from the first login shell after
/// the reboot, via a self-removing script hooked into every login-shell rc
/// file the user's shell might read: bash reads the first of
/// `.bash_profile`/`.bash_login`/`.profile` (so `.profile` alone misses
/// `.bash_profile` users) plus `.bashrc`; zsh reads only `.zprofile`/`.zshrc`;
/// fish gets a `conf.d` drop-in. The stored boot id makes the script fire only
/// after an actual reboot; past a two-week deadline it only cleans itself up
/// (an unfired hook must expire, not surprise-run months later); and the
/// resumed build is detached into the background with a log file so login
/// shells and display managers sourcing an rc file never block on it.
fn schedule_resume_unix() -> Result<String, String> {
    use std::time::{SystemTime, UNIX_EPOCH};
    let (repo, cargo) = resume_ingredients();
    let (repo_q, cargo_q) = (sh_quote(&repo), sh_quote(&cargo));
    let home_s = std::env::var("HOME").map_err(|_| "HOME is not set".to_string())?;
    let home = Path::new(&home_s);
    let script_path = home.join(".formal-setup-resume.sh");
    let boot_id = fs::read_to_string("/proc/sys/kernel/random/boot_id")
        .unwrap_or_default()
        .trim()
        .to_string();
    if boot_id.is_empty() {
        // Without a boot id the script cannot tell a reboot happened; it would
        // either never fire or fire immediately. Fall back to a manual re-run.
        return Err(
            "cannot read /proc/sys/kernel/random/boot_id (needed to detect the reboot)".to_string(),
        );
    }
    let deadline = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0)
        + 14 * 24 * 60 * 60;
    let script = format!(
        r#"#!/bin/sh
# formal setup: resume `cargo build` once after the reboot, then remove itself.
# Hooked from the rc lines tagged formal-setup-resume; the boot-id check makes
# it fire only after an actual reboot, and past the deadline it only cleans up.
if [ "$(cat /proc/sys/kernel/random/boot_id 2>/dev/null)" != "{boot_id}" ]; then
    for rc in "$HOME/.profile" "$HOME/.bash_profile" "$HOME/.bash_login" "$HOME/.bashrc" "$HOME/.zprofile" "$HOME/.zshrc"; do
        # readlink -f: sed -i through a symlink would replace it with a plain
        # file (breaking dotfiles setups); edit the real file instead.
        [ -f "$rc" ] && sed -i '/formal-setup-resume/d' "$(readlink -f "$rc")" 2>/dev/null
    done
    rm -f "$HOME/.config/fish/conf.d/formal-setup-resume.fish"
    rm -f "$HOME/.formal-setup-resume.sh"
    if [ "$(date +%s)" -lt {deadline} ]; then
        echo "formal setup: resuming cargo build (log: $HOME/.formal-setup-resume.log)"
        (cd {repo_q} && FORMAL_SETUP=install nohup {cargo_q} build >"$HOME/.formal-setup-resume.log" 2>&1 &)
    fi
fi
"#
    );
    fs::write(&script_path, script)
        .map_err(|e| format!("writing {}: {e}", script_path.display()))?;

    // The hook line is valid sh, bash and zsh alike.
    let hook = "[ -f \"$HOME/.formal-setup-resume.sh\" ] && . \"$HOME/.formal-setup-resume.sh\" # formal-setup-resume\n";
    let shell = std::env::var("SHELL").unwrap_or_default();
    let mut hooked: Vec<String> = Vec::new();
    for rc in [
        ".profile",
        ".bash_profile",
        ".bash_login",
        ".bashrc",
        ".zprofile",
        ".zshrc",
    ] {
        let rc_path = home.join(rc);
        if !rc_path.exists() {
            continue;
        }
        let contents = fs::read_to_string(&rc_path).unwrap_or_default();
        if !contents.contains("formal-setup-resume") {
            use std::io::Write;
            let mut f = fs::OpenOptions::new()
                .append(true)
                .open(&rc_path)
                .map_err(|e| format!("opening {}: {e}", rc_path.display()))?;
            f.write_all(format!("\n{hook}").as_bytes())
                .map_err(|e| format!("appending to {}: {e}", rc_path.display()))?;
        }
        hooked.push(format!("~/{rc}"));
    }
    // fish reads none of the above; give it a conf.d drop-in running the same
    // script (which deletes the drop-in when it fires).
    let fish_conf = home.join(".config/fish/conf.d");
    if fish_conf.is_dir() || shell.ends_with("fish") {
        fs::create_dir_all(&fish_conf)
            .map_err(|e| format!("creating {}: {e}", fish_conf.display()))?;
        fs::write(
            fish_conf.join("formal-setup-resume.fish"),
            "# formal-setup-resume: run the pending formal setup resume (it removes itself).\n\
             test -f \"$HOME/.formal-setup-resume.sh\"; and sh \"$HOME/.formal-setup-resume.sh\"\n",
        )
        .map_err(|e| format!("writing the fish hook: {e}"))?;
        hooked.push("fish conf.d".to_string());
    }
    if hooked.is_empty() {
        let rc_path = home.join(".profile");
        fs::write(&rc_path, hook).map_err(|e| format!("writing {}: {e}", rc_path.display()))?;
        hooked.push("~/.profile".to_string());
        if shell.ends_with("zsh") {
            let z = home.join(".zprofile");
            fs::write(&z, hook).map_err(|e| format!("writing {}: {e}", z.display()))?;
            hooked.push("~/.zprofile".to_string());
        }
    }
    Ok(format!(
        "`cargo build` is scheduled to re-run from your next login shell (hook in {})",
        hooked.join(", ")
    ))
}

/// Initiate the reboot the user just approved; returns whether it was accepted
/// by the system.
fn reboot_now() -> bool {
    if cfg!(windows) {
        // A short delay so the report above still reaches the terminal.
        runs(
            "shutdown",
            &[
                "/r",
                "/t",
                "10",
                "/c",
                "formal setup: rebooting to finish installing dependencies",
            ],
        )
    } else {
        // The same 10-second grace as Windows (detached, so this call returns):
        // the reboot report above is emitted by cargo only after this build
        // script exits, and an immediate shutdown would race that flush. The
        // sudo credential is usually still cached from the apt install moments
        // earlier (`-n` = fail instead of prompting); otherwise prompt, then
        // fall back to systemd's polkit path for desktop sessions.
        let delayed = "(sleep 10 && shutdown -r now) </dev/null >/dev/null 2>&1 &";
        runs("sudo", &["-n", "sh", "-c", delayed])
            || runs("sudo", &["sh", "-c", delayed])
            || runs(
                "sh",
                &[
                    "-c",
                    "(sleep 10 && systemctl reboot) </dev/null >/dev/null 2>&1 &",
                ],
            )
    }
}

/// A dependency was installed but needs a reboot to finish: ask on the console,
/// and on `y` schedule the post-login resume (see `schedule_resume_*`) and
/// reboot. Idempotency makes the resumed `cargo build` continue exactly where
/// this run left off. Declining, or having no console, reports what to do.
fn offer_reboot(report: &mut Report, why: &str) {
    let manual = "reboot manually, then re-run `cargo build`; it picks up where it left off";
    match prompt_yes(&format!(
        "formal setup: {why}\nReboot now? (`cargo build` will be scheduled to re-run and continue after you log back in.)"
    )) {
        None => report.note(format!("{why} No console to ask on; {manual}.")),
        Some(false) => report.note(format!("{why} Reboot declined; {manual}.")),
        Some(true) => {
            // Schedule the resume first so the reboot cannot outrun it; if
            // scheduling fails the user still asked to reboot, so reboot anyway
            // and tell them the re-run is manual.
            let how = match if cfg!(windows) {
                schedule_resume_windows()
            } else {
                schedule_resume_unix()
            } {
                Ok(how) => how,
                Err(e) => {
                    format!("(could not schedule the automatic re-run: {e}; re-run `cargo build` manually after the reboot)")
                }
            };
            if reboot_now() {
                report.note(format!("{why} Rebooting now; {how}."));
            } else {
                report.note(format!("{why} Could not initiate the reboot; {manual}. {how}."));
            }
        }
    }
}

/// Windows host: the QEMU boots and the toolchain live inside WSL (see
/// `tests/common/mod.rs`), so the work is to ensure WSL exists, then provision
/// the Linux side of it.
fn setup_windows(report: &mut Report, install: bool) {
    // Every Windows that supports `wsl --install` ships an in-box wsl.exe stub
    // in System32, so wsl being on PATH proves nothing; only a successful
    // `wsl --status` means the WSL platform is actually installed (the stub
    // exits nonzero with "not installed").
    let have_wsl = runs("wsl", &["--status"]);
    if !have_wsl {
        if install {
            // Try `wsl --install` directly first: with an administrator token
            // (an admin terminal, or any Windows OpenSSH session of an admin
            // user) it works with no UAC ceremony - and `Start-Process -Verb
            // RunAs` is unreliable from non-interactive sessions. Its exit
            // code is useless either way (nonzero even on success while a
            // reboot is pending), so judge by the ground truth instead: the
            // optional-feature state. Fall back to a UAC elevation request
            // only when the direct run left the features untouched.
            let _ = runs("wsl", &["--install"]);
            if !wsl_features_coming() {
                elevate_windows(report, "WSL", "wsl --install");
            }
            if wsl_features_coming() {
                report.note("WSL: features enabled (the distribution follows after the reboot).");
                offer_reboot(
                    report,
                    "WSL is installed, but Windows must reboot to finish enabling it.",
                );
            } else {
                report.note(
                    "WSL: could not be installed automatically. Run in an admin shell:  wsl --install",
                );
            }
        } else {
            report.note(
                "WSL is not installed. Install it (admin PowerShell, then reboot):  wsl --install",
            );
        }
        return;
    }

    // Right after a `wsl --install` + reboot the platform is enabled but the
    // Ubuntu distribution may still be completing its first-run setup, in which
    // case the apt provisioning below cannot run yet.
    if !runs("wsl", &["-e", "true"]) {
        report.note(
            "WSL is installed but no Linux distribution is ready yet (after `wsl --install`, \
             Ubuntu finishes setting up on its first launch). Run `wsl` once to let it finish \
             (or install one with `wsl --install -d Ubuntu`), then re-run `cargo build`.",
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
    let deps: Vec<(&str, &str, &str)> = vec![
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
            // Mirrors how tests/common finds it: PATH, then the toolchain
            // release's bin/ (which bundles qemu-riscv64), then RISCV_BIN.
            "command -v qemu-riscv64 \
             || [ -x \"$HOME/riscv-toolchain/riscv/bin/qemu-riscv64\" ] \
             || { [ -n \"$RISCV_BIN\" ] && [ -x \"$RISCV_BIN/qemu-riscv64\" ]; }",
            "qemu-user",
            "user-mode QEMU (qemu-riscv64, for the hosted Linux-program tests)",
        ),
        (
            "command -v mpicc",
            "libopenmpi-dev openmpi-bin",
            "system MPI (for the --features hpc distributed backend)",
        ),
        // clang/libclang belong with MPI, not behind CARGO_FEATURE_HPC: rsmpi's
        // `mpi-sys` runs bindgen, and within one `cargo build --features hpc`
        // there is no ordering between this script's apt and mpi-sys's bindgen,
        // so the toolchain must already be present from the plain build. The
        // probe demands the clang driver (its builtin headers provide stddef.h)
        // AND the real libclang - `grep -q libclang` alone is fooled by
        // libclang-cpp.so, which bindgen cannot use.
        (
            "command -v clang >/dev/null && ldconfig -p 2>/dev/null | grep -Eq 'libclang(-[0-9]+)?\\.so'",
            "clang libclang-dev",
            "clang/libclang (for rsmpi's bindgen, --features hpc)",
        ),
    ];

    let missing: Vec<&(&str, &str, &str)> = deps.iter().filter(|(p, _, _)| !present(p)).collect();
    if missing.is_empty() {
        return;
    }

    if !install {
        for (_, pkgs, human) in &missing {
            report.note(format!(
                "{human}: missing. Install with:  sudo apt-get install -y {pkgs}"
            ));
        }
        return;
    }

    let pkgs: Vec<&str> = missing.iter().flat_map(|(_, p, _)| p.split(' ')).collect();
    let pkg_list = pkgs.join(" ");

    if via_wsl {
        // Windows host: install inside WSL as root. `wsl -u root` is privileged in
        // the distribution without a Windows UAC prompt or a WSL password, so no
        // escalation dialog is needed for these. `dpkg --configure -a` first
        // self-heals a previously-interrupted dpkg (a common stuck state).
        // (A reboot-required flag inside the distribution would concern the WSL
        // VM, not the Windows host, so no reboot handling here.)
        let apt = format!(
            "DEBIAN_FRONTEND=noninteractive dpkg --configure -a && apt-get update \
             && DEBIAN_FRONTEND=noninteractive apt-get install -y {pkg_list}"
        );
        try_install(
            report,
            "WSL apt packages (installed as root via `wsl -u root`)",
            "wsl",
            &["-u", "root", "-e", "bash", "-lc", &apt],
        );
    } else {
        // Native Linux host: escalate with `sudo`, which prompts for the
        // password on the controlling terminal. Cargo nulls a build script's
        // stdin and pipes its output, so the std streams say nothing about
        // interactivity; console() is the real test (an openable /dev/tty AND
        // this build in its foreground, and not CI). With no console but an
        // explicit `FORMAL_SETUP=install` (the CI opt-in), `sudo -n` is used
        // instead: it never prompts, so it either works (passwordless sudo,
        // the standard CI configuration) or fails fast into the instruction
        // note. Anything else instructs instead of hanging.
        let explicit_install = std::env::var("FORMAL_SETUP").as_deref() == Ok("install");
        let sudo = if console().is_some() {
            Some("sudo")
        } else if explicit_install {
            Some("sudo -n")
        } else {
            None
        };
        if let Some(sudo) = sudo {
            let reboot_already_pending = Path::new("/var/run/reboot-required").exists();
            let apt = format!(
                "{sudo} dpkg --configure -a && {sudo} apt-get update \
                 && {sudo} DEBIAN_FRONTEND=noninteractive apt-get install -y {pkg_list}"
            );
            let installed = try_install(report, "apt packages (via sudo)", "sh", &["-c", &apt]);
            // apt can pull in packages (a kernel, libc) whose postinst requests
            // a reboot; offer to do it now and resume setup afterwards. Only a
            // flag this install newly created counts - a pre-existing one is
            // from unrelated updates.
            if installed
                && !reboot_already_pending
                && Path::new("/var/run/reboot-required").exists()
            {
                offer_reboot(
                    report,
                    "the packages just installed request a reboot to take effect.",
                );
            }
        } else {
            report.note(format!(
                "missing packages (no terminal to prompt for sudo); run:  sudo apt-get install -y {pkg_list}"
            ));
        }
    }

    // The toolchain the QEMU tests default to (`$HOME/riscv-toolchain/...`) is a
    // specific upstream release, not the apt package; if the boot tests still
    // cannot find it, point `RISCV_BIN` at whatever `as`/`ld` apt installed.
    report.note(
        "if a QEMU boot test reports a missing toolchain, set RISCV_BIN to the dir holding \
         riscv64-unknown-elf-as/ld (apt installs them on PATH; export RISCV_BIN accordingly).",
    );
}

/// Whether the WSL Windows features are enabled or pending-enable: the ground
/// truth `wsl --install` leaves behind (its exit code is nonzero even on
/// success while the reboot is pending). The PowerShell enum prints
/// locale-independently ("Enabled"/"EnablePending"; "Disabled" never contains
/// a capital-E "Enable"). Needs an admin token, like the install itself; for
/// a non-admin user this stays false and setup conservatively reports the
/// manual command even if a UAC-elevated install succeeded.
fn wsl_features_coming() -> bool {
    Command::new("powershell")
        .args([
            "-NoProfile",
            "-Command",
            "(Get-WindowsOptionalFeature -Online -FeatureName Microsoft-Windows-Subsystem-Linux).State; \
             (Get-WindowsOptionalFeature -Online -FeatureName VirtualMachinePlatform).State",
        ])
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).matches("Enable").count() >= 2)
        .unwrap_or(false)
}

/// Request Windows privilege escalation (a UAC prompt) and run `command` in the
/// elevated shell, waiting for it; returns whether it exited successfully (for
/// `wsl --install` the caller must judge by `wsl_features_coming` instead,
/// since that command's exit code is unreliable). Used for the only host-admin
/// action: installing WSL itself.
fn elevate_windows(report: &mut Report, human: &str, command: &str) -> bool {
    // PowerShell `Start-Process -Verb RunAs` raises the UAC dialog; `-Wait
    // -PassThru` blocks until the elevated `cmd /c <command>` finishes and
    // surfaces its exit code. Declining the UAC dialog makes Start-Process
    // throw, but under `-Command` the next statement still runs with
    // `$p = $null`, and `exit $null` exits 0 - so the try/catch plus the null
    // guard are what actually turn a decline into a failure exit code.
    let ps = format!(
        "try {{ $p = Start-Process -Verb RunAs -Wait -PassThru -FilePath cmd.exe \
         -ArgumentList '/c {command}' -ErrorAction Stop; \
         if ($null -eq $p.ExitCode) {{ exit 1 }}; exit $p.ExitCode }} catch {{ exit 1 }}"
    );
    match Command::new("powershell")
        .args(["-NoProfile", "-Command", &ps])
        .status()
    {
        Ok(s) => s.success(),
        Err(e) => {
            report.note(format!(
                "{human}: could not request elevation ({e}). Run in an admin shell:  {command}"
            ));
            false
        }
    }
}
