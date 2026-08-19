//! Factory-default setup end-to-end test.
//!
//! Boots an **empty factory-default Linux machine** as a local VM (QEMU/KVM),
//! then does exactly what a new user does: install Rust by the documented
//! steps, unpack this repository, run `cargo build` (the single setup entry
//! point) on a real terminal (`ssh -tt`, so setup's console prompts genuinely
//! appear and a piped `y` answers the reboot question), ride through the
//! reboot when setup requests one, and finally run the full test suite inside
//! the guest. No shims: the guest runs the real installers against a real
//! empty system, and the test plays the human at the terminal (CLAUDE.md: one
//! real end-to-end approach).
//!
//! (A Windows sibling existed and proved setup's WSL-install/reboot/
//! resume flow on a factory Server guest, but WSL2 inside a guest needs a
//! virtualisation depth no Windows host or hosted runner provides, so it was
//! removed; `git log -- tests/setup_e2e/windows` has the full recipe and
//! findings should it return.)
//!
//! The test is `#[ignore]`d: it downloads an image once, saturates the
//! machine (about 3 minutes on a 24-core host; expect longer on modest
//! hardware), and needs virtualisation the host may not have. Run it
//! deliberately:
//!
//! ```sh
//! cargo nextest run --run-ignored all -E 'test(factory_default_linux)'
//! ```
//!
//! Requirements are probed up front; a missing one **fails** the test with
//! the exact command to install it (like the QEMU boot tests: asking for the
//! test gets you a result or a reason, never a silent skip). Live progress
//! streams to `target/tmp/test-logs/<test>/e2e.progress`; every driver
//! command and its output is appended to `.../driver.log`, and the long
//! in-guest transcripts (prep, builds, suite) each get their own tail-able
//! `.log` beside it.
//!
//! Recursion guard: every in-guest command runs with `FORMAL_E2E_INNER=1`
//! set, and the test fails immediately (loudly, per the suite's no-silent-
//! skip convention) when that variable is present, so the suite running
//! inside a guest can never boot a VM inside the VM (the `#[ignore]` already
//! keeps it out of a plain `cargo nt`; this is the belt to that suspender).
//!
//! See DEVELOPMENT.md §6.2 for the full description and the CI wiring.

#[path = "../common/mod.rs"]
mod common;

use common::{script_path, test_log_dir, toolchain_shell, Progress};
use std::io::Write as _;
use std::time::{Duration, Instant};

/// Host loopback port the guest's SSH is forwarded to. Fixed (deterministic
/// runs, findable in `driver.log`); a collision fails the boot fast.
const LINUX_SSH_PORT: u16 = 2261;

/// The factory-default Linux the guest boots: the current Ubuntu LTS server
/// cloud image. "Factory default" deliberately tracks what a user installs
/// today; delete the cached copy under `~/.cache/formal-e2e/images` (in the
/// shell environment) to refresh it.
const UBUNTU_IMAGE_URL: &str =
    "https://cloud-images.ubuntu.com/noble/current/noble-server-cloudimg-amd64.img";

/// The recursion-guard variable exported into every in-guest command.
const INNER_MARKER: &str = "FORMAL_E2E_INNER";

// ---------------------------------------------------------------------------
// Driver plumbing. Host-side commands run through `common::toolchain_shell`
// (bash; through WSL on a Windows host - the same environment the QEMU boot
// tests already use), so one driver works from either host OS.
// ---------------------------------------------------------------------------

/// Appends `entry` to `target/tmp/test-logs/<test>/driver.log`.
fn log_driver(entry: &str) {
    let path = format!("{}/driver.log", test_log_dir());
    if let Ok(mut f) = std::fs::OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
    {
        let _ = writeln!(f, "{entry}");
    }
}

/// Runs `script` in the shell environment, recording the script and output in
/// `driver.log`. Panics only if the shell itself cannot launch.
fn sh(script: &str) -> std::process::Output {
    let out = toolchain_shell(script).output().unwrap_or_else(|e| {
        panic!("cannot launch the shell environment (on Windows: WSL) that drives the VM: {e}")
    });
    log_driver(&format!(
        "$ {script}\n--- status {} ---\n{}{}",
        out.status,
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    ));
    out
}

/// `sh`, asserting success; returns stdout. `what` names the step on failure.
fn sh_ok(what: &str, script: &str) -> String {
    let out = sh(script);
    assert!(
        out.status.success(),
        "{what} failed (full transcript: {}/driver.log)\n$ {script}\n--- stdout ---\n{}--- stderr ---\n{}",
        test_log_dir(),
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// Probes one requirement; failure fails the test with the exact fix.
fn require(what: &str, probe: &str, fix: &str) {
    let out = sh(probe);
    assert!(
        out.status.success(),
        "requirement missing: {what}\n  fix: {fix}\n  (probe: {probe})"
    );
}

/// The recursion guard: refuses (loudly - a green vacuous pass would violate
/// the suite's fail-loud convention) to boot a VM when already inside a
/// factory guest. Unreachable in the designed flow, since the in-guest suite
/// never passes `--run-ignored`; it only fires when someone explicitly asks
/// for the test inside a guest, or the marker leaked into their shell.
fn inner_guard() {
    assert!(
        std::env::var_os(INNER_MARKER).is_none(),
        "{INNER_MARKER} is set: refusing to boot a VM inside a factory guest \
         (or the marker leaked into this shell; unset it to run the test)"
    );
}

/// Plain connection facts for one booted guest.
struct Vm {
    /// Host loopback port forwarded to the guest's SSH.
    port: u16,
    /// Guest login user.
    user: &'static str,
    /// Private-key path, in the shell environment that runs ssh/qemu.
    key: String,
}

/// The ssh invocation prefix for `vm`. The guest is throwaway and bound to
/// loopback, so host-key churn is silenced rather than persisted.
fn ssh_base(vm: &Vm) -> String {
    format!(
        "ssh -i '{}' -p {} -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null \
         -o LogLevel=ERROR -o ConnectTimeout=5 {}@127.0.0.1",
        vm.key, vm.port, vm.user
    )
}

/// Runs a short in-guest command, asserting success; returns its output.
fn ssh_ok(vm: &Vm, what: &str, cmd: &str, secs: u64) -> String {
    sh_ok(what, &format!("timeout {secs} {} '{cmd}'", ssh_base(vm)))
}

/// Runs a short in-guest command, returning its raw outcome.
fn ssh_try(vm: &Vm, cmd: &str, secs: u64) -> std::process::Output {
    sh(&format!("timeout {secs} {} '{cmd}'", ssh_base(vm)))
}

/// Waits until the guest's SSH is up (`up = true`) or gone (`up = false`).
fn wait_ssh(vm: &Vm, up: bool, what: &str, deadline: Duration, progress: &mut Progress) {
    let started = Instant::now();
    while started.elapsed() < deadline {
        progress.update(|| format!("{what}: {:.0}s", started.elapsed().as_secs_f32()));
        // `exit 0`: the cheapest liveness probe (shell-agnostic).
        let alive = sh(&format!("{} 'exit 0'", ssh_base(vm))).status.success();
        if alive == up {
            return;
        }
        std::thread::sleep(Duration::from_secs(5));
    }
    panic!(
        "{what}: gave up after {:.0}s (guest console: {}/serial.log)",
        deadline.as_secs_f32(),
        test_log_dir()
    );
}

/// Runs a long in-guest command, streaming the transcript to
/// `target/tmp/test-logs/<test>/<log_name>.log` for live tailing. With
/// `pty` the command runs under `ssh -tt` (a real terminal, so setup's
/// console prompts appear and the piped `y` answers the reboot question if
/// it comes) - use it for the `cargo build` phases, whose prompts are part
/// of what is under test. Without it the command gets no terminal (plain
/// line output; nextest would otherwise render its live progress bar as
/// escape codes all over the transcript). Returns (exited zero, transcript).
fn ssh_stream(
    vm: &Vm,
    what: &str,
    cmd: &str,
    log_name: &str,
    secs: u64,
    progress: &mut Progress,
    pty: bool,
) -> (bool, String) {
    let host_log = format!("{}/{log_name}.log", test_log_dir());
    let _ = std::fs::remove_file(&host_log);
    let log_env = script_path(&host_log);
    // `y\r` (CR): a pty in canonical mode maps CR to NL via ICRNL, and CR is
    // what a real Enter key sends.
    let script = if pty {
        // Process substitution, not a plain pipe: stdin stays open for the
        // session's lifetime (some sshd/pty stacks tear the session down on
        // stdin EOF before the command runs; the leftover `sleep` dies on
        // its own).
        format!(
            "timeout {secs} {} -tt '{cmd}' < <(printf 'y\\r'; sleep {secs}) >\"{log_env}\" 2>&1",
            ssh_base(vm)
        )
    } else {
        format!(
            "timeout {secs} {} '{cmd}' </dev/null >\"{log_env}\" 2>&1",
            ssh_base(vm)
        )
    };
    log_driver(&format!("$ {script}"));
    let worker = {
        let script = script.clone();
        std::thread::spawn(move || toolchain_shell(&script).output())
    };
    let started = Instant::now();
    while !worker.is_finished() {
        progress.update(|| {
            let lines = std::fs::read_to_string(&host_log)
                .map(|t| t.lines().count())
                .unwrap_or(0);
            format!(
                "{what}: {:.0}s, {lines} transcript lines ({log_name}.log)",
                started.elapsed().as_secs_f32()
            )
        });
        std::thread::sleep(Duration::from_millis(200));
    }
    let out = worker
        .join()
        .expect("the ssh worker thread panicked")
        .expect("launching ssh failed");
    let transcript = std::fs::read_to_string(&host_log).unwrap_or_default();
    log_driver(&format!(
        "--- {what}: status {} ({} transcript bytes in {log_name}.log) ---",
        out.status,
        transcript.len()
    ));
    (out.status.success(), transcript)
}

/// Writes `content` to the test log dir as `name` and copies it into the
/// guest's home directory (scripts sidestep three layers of quoting).
fn push_file(vm: &Vm, name: &str, content: &str) {
    let host = format!("{}/{name}", test_log_dir());
    std::fs::write(&host, content).expect("write guest script");
    let src = script_path(&host);
    sh_ok(
        &format!("upload {name} into the guest"),
        &format!(
            "scp -i '{}' -P {} -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null \
             -o LogLevel=ERROR \"{src}\" {}@127.0.0.1:{name}",
            vm.key, vm.port, vm.user
        ),
    );
}

/// Packs the repository working tree (tracked + untracked-but-not-ignored
/// files: what a fresh checkout plus your edits contains; `target/` is
/// ignored) into `<work>/repo.tar` in the shell environment.
fn stage_repo(work: &str) {
    let root = env!("CARGO_MANIFEST_DIR");
    // Staged under the per-test log dir, beside the run's other artifacts.
    // Relative paths keep a drive-letter colon out of tar's arguments (GNU
    // tar would read `C:` as a remote host).
    let rel = format!("target/tmp/test-logs/{}", common::test_name());
    std::fs::create_dir_all(format!("{root}/{rel}")).expect("create the staging dir");
    let list = std::process::Command::new("git")
        .args(["ls-files", "-co", "--exclude-standard"])
        .current_dir(root)
        .output()
        .expect("git is required to enumerate the working tree");
    assert!(
        list.status.success(),
        "git ls-files failed: {}",
        String::from_utf8_lossy(&list.stderr)
    );
    std::fs::write(format!("{root}/{rel}/filelist.txt"), &list.stdout)
        .expect("write the file list");
    // The host tar (bsdtar on Windows, GNU tar on Linux; both read -T lists).
    let tar = std::process::Command::new("tar")
        .args([
            "-cf",
            &format!("{rel}/repo.tar"),
            "-T",
            &format!("{rel}/filelist.txt"),
        ])
        .current_dir(root)
        .output()
        .expect("tar is required to pack the working tree");
    assert!(
        tar.status.success(),
        "tar failed: {}",
        String::from_utf8_lossy(&tar.stderr)
    );
    let src = script_path(&format!("{root}/{rel}/repo.tar"));
    sh_ok(
        "copy repo.tar into the VM workspace",
        &format!("cp \"{src}\" '{work}/repo.tar'"),
    );
}

/// Kills the QEMU whose pidfile lives in `work` (a stale one from a previous
/// run, or this run's on teardown). Best-effort by design.
fn kill_qemu(work: &str) {
    let _ = sh(&format!(
        "[ -f '{work}/qemu.pid' ] && kill \"$(cat '{work}/qemu.pid')\" 2>/dev/null; \
         rm -f '{work}/qemu.pid'"
    ));
}

/// Tears the guest down even when a phase panics.
struct VmGuard {
    work: String,
}
impl Drop for VmGuard {
    fn drop(&mut self) {
        kill_qemu(&self.work);
    }
}

/// The guest CPU count: all host cores minus two of headroom (the in-guest
/// compiles dominate the wall-clock, so the guest gets the machine).
fn guest_cpus() -> u32 {
    let n = sh_ok("count host CPUs", "nproc")
        .trim()
        .parse::<u32>()
        .unwrap_or(4);
    n.saturating_sub(2).clamp(2, 32)
}

/// The absolute `$HOME` of the shell environment (resolved once so workspace
/// paths can be single-quoted everywhere without expansion surprises).
fn env_home() -> String {
    let home = sh_ok("resolve the environment home", "printf %s \"$HOME\"");
    assert!(
        home.starts_with('/'),
        "unexpected $HOME in the shell environment: {home:?}"
    );
    home
}

/// The VM-driving requirements, each failing with its exact fix (the install
/// commands get the inside-WSL note when the host is Windows).
fn require_vm_tooling() {
    let wsl = if cfg!(windows) { " (inside WSL)" } else { "" };
    require(
        "the shell environment (on Windows: WSL)",
        "true",
        "install WSL:  wsl --install  (then reboot)",
    );
    require(
        "qemu-system-x86_64 (boots the factory guest)",
        "command -v qemu-system-x86_64",
        &format!("sudo apt-get install -y qemu-system-x86{wsl}"),
    );
    require(
        "qemu-img (creates the copy-on-write guest disk)",
        "command -v qemu-img",
        &format!("sudo apt-get install -y qemu-utils{wsl}"),
    );
    require(
        "an ISO builder (packs the cloud-init seed)",
        "command -v genisoimage || command -v mkisofs",
        &format!("sudo apt-get install -y genisoimage{wsl}"),
    );
    require(
        "the OpenSSH client (drives the guest)",
        "command -v ssh && command -v scp && command -v ssh-keygen",
        &format!("sudo apt-get install -y openssh-client{wsl}"),
    );
    require(
        "curl (downloads the guest image)",
        "command -v curl",
        &format!("sudo apt-get install -y curl{wsl}"),
    );
    require(
        "KVM access (/dev/kvm readable + writable)",
        "[ -r /dev/kvm ] && [ -w /dev/kvm ]",
        "add yourself to the kvm group:  sudo usermod -aG kvm $USER  (then re-login). \
         On a Windows host, WSL2 needs nested virtualisation (default-on under Windows 11; \
         `[wsl2] nestedVirtualization=true` in .wslconfig). On a GitHub runner:  \
         echo 'KERNEL==\"kvm\", GROUP=\"kvm\", MODE=\"0666\", OPTIONS+=\"static_node=kvm\"' \
         | sudo tee /etc/udev/rules.d/99-kvm4all.rules && sudo udevadm control --reload-rules \
         && sudo udevadm trigger --name-match=kvm",
    );
}

/// The ISO builder present on this system (probed by `require_vm_tooling`).
fn iso_tool() -> &'static str {
    if sh("command -v genisoimage").status.success() {
        "genisoimage"
    } else {
        "mkisofs"
    }
}

/// Asserts a `cargo build` transcript shows a silent setup: after a completed
/// setup, a re-run must find every dependency present and print nothing.
fn assert_setup_silent(what: &str, ok: bool, transcript: &str) {
    assert!(ok, "{what}: the build failed (see its .log)");
    assert!(
        !transcript.contains("formal setup:"),
        "{what}: setup still reports missing/just-installed dependencies after a completed \
         setup; it must be silent (idempotent + complete). Transcript tail:\n{}",
        transcript
            .lines()
            .rev()
            .take(30)
            .collect::<Vec<_>>()
            .into_iter()
            .rev()
            .collect::<Vec<_>>()
            .join("\n")
    );
}

// ---------------------------------------------------------------------------
// The factory-default Linux test.
// ---------------------------------------------------------------------------

#[test]
#[ignore = "boots a factory-default Linux VM and runs full setup + the whole suite inside \
            (about 3 minutes on a 24-core host; downloads a cloud image once). DEVELOPMENT.md §6.2."]
fn factory_default_linux() {
    inner_guard();
    let _ = std::fs::remove_file(format!("{}/driver.log", test_log_dir()));
    let mut progress = Progress::new("e2e");

    // --- requirements -----------------------------------------------------
    progress.update(|| "probing requirements".to_string());
    require_vm_tooling();

    // --- workspace + factory image ----------------------------------------
    let home = env_home();
    let work = format!("{home}/.cache/formal-e2e/linux");
    let images = format!("{home}/.cache/formal-e2e/images");
    kill_qemu(&work); // a stale guest from an aborted previous run
    sh_ok(
        "create the VM workspace",
        &format!("mkdir -p '{work}' '{images}'"),
    );
    let base = format!("{images}/ubuntu-noble-server-amd64.img");
    progress.update(|| "fetching the Ubuntu cloud image (cached after the first run)".to_string());
    sh_ok(
        "download the Ubuntu cloud image",
        &format!(
            "[ -f '{base}' ] || {{ curl -fSL --retry 3 -o '{base}.tmp' '{UBUNTU_IMAGE_URL}' \
             && mv '{base}.tmp' '{base}'; }}"
        ),
    );

    // --- per-run key, seed ISO, factory-fresh disk -------------------------
    let vm = Vm {
        port: LINUX_SSH_PORT,
        user: "ubuntu",
        key: format!("{work}/id"),
    };
    sh_ok(
        "generate the throwaway guest key",
        &format!(
            "rm -f '{work}/id' '{work}/id.pub' && ssh-keygen -q -t ed25519 -N '' -f '{work}/id'"
        ),
    );
    let pubkey = sh_ok("read the public key", &format!("cat '{work}/id.pub'"));
    // The only deviation from factory state: the cloud image has no accounts,
    // so cloud-init (the image's own first-boot mechanism) is given the key
    // for its default user - the moral equivalent of typing a password at the
    // installer.
    // The bootcmd stops Ubuntu's background auto-updates: on a factory image
    // they grab the dpkg lock minutes after every boot and would race the
    // real apt runs under test. The swapfile stands in for the swap any real
    // installation has (cloud images alone omit it): without it the suite's
    // memory-heavy verifier tests, 20+ at once, get null allocations and
    // abort. Operator machine-configuration, not a shim (setup itself is
    // untouched); the bootcmd runs on every boot, so it also covers the
    // post-reboot resumed build.
    let user_data = format!(
        "#cloud-config\n\
         ssh_authorized_keys:\n  - {}\n\
         swap:\n  filename: /swap.img\n  size: 8589934592\n  maxsize: 8589934592\n\
         bootcmd:\n  - [sh, -c, \"systemctl stop --no-block apt-daily.timer apt-daily-upgrade.timer || true; \
         systemctl mask --now apt-daily.service apt-daily-upgrade.service unattended-upgrades.service || true\"]\n",
        pubkey.trim()
    );
    let seed_dir = test_log_dir();
    std::fs::write(format!("{seed_dir}/user-data"), user_data).expect("write user-data");
    std::fs::write(
        format!("{seed_dir}/meta-data"),
        "instance-id: formal-e2e\nlocal-hostname: factory\n",
    )
    .expect("write meta-data");
    let seed_src = script_path(&seed_dir);
    sh_ok(
        "build the cloud-init seed ISO",
        &format!(
            "{} -output '{work}/seed.iso' -volid cidata -joliet -rock \
             \"{seed_src}/user-data\" \"{seed_src}/meta-data\"",
            iso_tool()
        ),
    );
    sh_ok(
        "create the factory-fresh overlay disk",
        &format!(
            "rm -f '{work}/disk.qcow2' && \
             qemu-img create -q -f qcow2 -b '{base}' -F qcow2 '{work}/disk.qcow2' 32G"
        ),
    );

    // --- boot ---------------------------------------------------------------
    let _guard = VmGuard { work: work.clone() };
    let serial = script_path(&format!("{}/serial.log", test_log_dir()));
    let cpus = guest_cpus();
    progress.update(|| "booting the factory guest".to_string());
    sh_ok(
        "boot the factory guest",
        &format!(
            "qemu-system-x86_64 -enable-kvm -cpu host -smp {cpus} -m 24576 \
             -drive file='{work}/disk.qcow2',if=virtio,cache=unsafe,discard=unmap \
             -drive file='{work}/seed.iso',media=cdrom \
             -netdev user,id=n0,hostfwd=tcp:127.0.0.1:{}-:22 -device virtio-net-pci,netdev=n0 \
             -display none -vnc 127.0.0.1:48 -serial file:\"{serial}\" -daemonize -pidfile '{work}/qemu.pid'",
            vm.port
        ),
    );
    wait_ssh(
        &vm,
        true,
        "waiting for the guest's SSH",
        Duration::from_secs(600),
        &mut progress,
    );
    let _ = ssh_try(&vm, "cloud-init status --wait >/dev/null 2>&1 || true", 600);

    // --- the documented human steps before `cargo build` -------------------
    stage_repo(&work);
    sh_ok(
        "copy the repository into the guest",
        &format!(
            "scp -i '{}' -P {} -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null \
             -o LogLevel=ERROR '{work}/repo.tar' {}@127.0.0.1:repo.tar",
            vm.key, vm.port, vm.user
        ),
    );
    push_file(
        &vm,
        "prep.sh",
        &format!(
            "#!/bin/sh\n\
             # Factory prep: the documented steps a human does before `cargo build`\n\
             # (README: install Rust via rustup; rustup's prerequisite is a C linker).\n\
             set -ex\n\
             export {INNER_MARKER}=1\n\
             # The lock timeout rides out any straggling first-boot apt activity.\n\
             sudo apt-get -o DPkg::Lock::Timeout=600 update\n\
             sudo DEBIAN_FRONTEND=noninteractive apt-get -o DPkg::Lock::Timeout=600 install -y build-essential\n\
             curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal\n\
             mkdir -p formal && tar -xf repo.tar -C formal\n"
        ),
    );
    let (ok, _) = ssh_stream(
        &vm,
        "guest prep (build-essential + rustup + unpack)",
        "sh prep.sh",
        "prep",
        1800,
        &mut progress,
        false,
    );
    assert!(ok, "guest prep failed (see prep.log)");

    // --- `cargo build` IS the setup ----------------------------------------
    // FORMAL_SETUP stays unset: that is the human flow, the guest has no CI
    // variables so setup installs by default, and it keeps the resume's own
    // FORMAL_SETUP=install a real env change (what re-runs build.rs).
    let (ok, build1) = ssh_stream(
        &vm,
        "first `cargo build` (runs setup for real)",
        &format!("cd formal && {INNER_MARKER}=1 $HOME/.cargo/bin/cargo build"),
        "build1",
        5400,
        &mut progress,
        true,
    );
    assert!(
        build1.contains("formal setup:"),
        "the first build on a factory machine reported no setup activity at all; the deps \
         cannot have been present. Transcript: build1.log"
    );
    assert!(
        build1.contains("installed."),
        "setup ran but installed nothing on a factory machine (see build1.log)"
    );
    // The reboot is announced by the report's "Rebooting now" note, but a dead
    // connection right after the "Reboot now?" prompt is the same event with
    // the note's flush lost to the shutdown.
    if build1.contains("Rebooting now") || (!ok && build1.contains("Reboot now?")) {
        // Setup asked for a reboot, we answered y: ride through it, then a
        // login shell fires the resume hook (nohup'd `cargo build`).
        wait_ssh(
            &vm,
            false,
            "waiting for the reboot",
            Duration::from_secs(600),
            &mut progress,
        );
        wait_ssh(
            &vm,
            true,
            "waiting for the guest to come back",
            Duration::from_secs(900),
            &mut progress,
        );
        ssh_ok(
            &vm,
            "trigger the login-shell resume hook",
            "timeout 60 bash -lc true",
            120,
        );
        let deadline = Instant::now() + Duration::from_secs(2700);
        loop {
            assert!(
                Instant::now() < deadline,
                "the post-reboot resumed build did not finish in time (guest log: \
                 ~/.formal-setup-resume.log)"
            );
            progress
                .update(|| "waiting for the resumed `cargo build` after the reboot".to_string());
            // `[c]argo` keeps the pattern from matching the polling shell's
            // own cmdline (with a redirection, bash stays resident and would
            // otherwise self-match, making `busy` permanently true).
            let busy = ssh_try(&vm, "pgrep -f \"[c]argo build\" >/dev/null", 30)
                .status
                .success();
            let resumed = ssh_try(&vm, "test -f .formal-setup-resume.log", 30)
                .status
                .success();
            if resumed && !busy {
                break;
            }
            std::thread::sleep(Duration::from_secs(15));
        }
    } else {
        assert!(ok, "the first `cargo build` failed (see build1.log)");
    }

    // --- the hpc feature provisions its extra deps the same way ------------
    let (ok, _) = ssh_stream(
        &vm,
        "`cargo build --features hpc` (provisions libclang)",
        &format!("cd formal && {INNER_MARKER}=1 $HOME/.cargo/bin/cargo build --features hpc"),
        "build-hpc",
        5400,
        &mut progress,
        true,
    );
    assert!(ok, "the --features hpc build failed (see build-hpc.log)");

    // --- setup must now be silent, and every dependency really present -----
    // FORMAL_SETUP=detect differs from every value the guest has seen (so the
    // env change genuinely re-runs build.rs rather than replaying a cached
    // result) and never installs, so silence here means complete.
    let (ok, build2) = ssh_stream(
        &vm,
        "re-run `cargo build` (must be silent)",
        &format!("cd formal && {INNER_MARKER}=1 FORMAL_SETUP=detect $HOME/.cargo/bin/cargo build"),
        "build2",
        3600,
        &mut progress,
        true,
    );
    assert_setup_silent("re-run after setup", ok, &build2);
    for (what, probe) in [
        ("QEMU system emulator", "qemu-system-riscv64 --version"),
        ("RISC-V assembler", "riscv64-unknown-elf-as --version"),
        ("user-mode QEMU", "qemu-riscv64 --version"),
        ("MPI compiler wrapper", "mpicc --version"),
    ] {
        ssh_ok(&vm, &format!("{what} present in the guest"), probe, 60);
    }

    // --- the full suite, inside the factory guest --------------------------
    ssh_ok(
        &vm,
        "install cargo-nextest (prebuilt)",
        "curl -LsSf https://get.nexte.st/latest/linux | tar zxf - -C $HOME/.cargo/bin",
        300,
    );
    let (ok, _) = ssh_stream(
        &vm,
        "the full test suite inside the factory guest",
        &format!(
            "cd formal && {INNER_MARKER}=1 PATH=$HOME/.cargo/bin:$PATH \
             cargo nextest run --no-fail-fast"
        ),
        "suite",
        10800,
        &mut progress,
        false,
    );
    assert!(
        ok,
        "the suite failed inside the factory guest (see suite.log)"
    );

    let _ = ssh_try(&vm, "sudo poweroff", 30);
    progress.finish("factory-default Linux: setup + suite passed");
}
