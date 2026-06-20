//! Shared helpers for the integration tests.
//!
//! Each test binary in `tests/` includes this module via `mod common;`, so some
//! helpers appear unused from any single test binary's perspective.
#![allow(dead_code)]

use formal::verifier_types::{AccessTransitions, AccessedRanges, TypeConfiguration};
use formal::*;
use std::collections::BTreeSet;
use std::io::Write;
use std::ptr::NonNull;
use std::time::{Duration, Instant};
use thousands::Separable;

/// The current test's name, sanitised for use as a path component. libtest /
/// nextest name the running thread after the test function (e.g.
/// `uart_hello::uart_hello`); `::` becomes `.` so it is a single path segment.
pub fn test_name() -> String {
    std::thread::current()
        .name()
        .unwrap_or("test")
        .replace("::", ".")
}

/// The per-test log directory `target/tmp/test-logs/<test name>/`, created on
/// demand. **All** of a test's `target/tmp` output (live progress streams,
/// blessed traces, HPC run logs) is grouped here, one directory per test, so the
/// logs are easy to find and do not collide across tests.
pub fn test_log_dir() -> String {
    let dir = format!(
        "{}/target/tmp/test-logs/{}",
        env!("CARGO_MANIFEST_DIR"),
        test_name()
    );
    let _ = std::fs::create_dir_all(&dir);
    dir
}

/// Streams a test phase's live progress to
/// `target/tmp/test-logs/<test>/<phase>.progress` instead of drawing on the
/// console.
///
/// The console belongs to the test runner: interactive output (spinners,
/// carriage returns) interleaves with nextest's own status display and corrupts
/// it, so tests report nothing live: the console carries only the runner's
/// concise per-test lines. To watch a long phase (the verifier explores ~2M
/// steps for `uart_hello`; QEMU runs a fixed boot timeout), follow the file:
///
/// ```powershell
/// Get-Content -Wait target\tmp\test-logs\uart_hello.uart_hello\verify.progress
/// ```
///
/// Updates are throttled (so calling [`Progress::update`] every verifier step
/// is cheap) and appended one line at a time; the file is truncated when the
/// phase starts and ends with a `done:` line.
pub struct Progress {
    file: Option<std::fs::File>,
    last: Instant,
}

impl Progress {
    const INTERVAL: Duration = Duration::from_millis(250);

    /// Creates `target/tmp/test-logs/<test>/<phase>.progress` (truncating any
    /// previous run's file). The test name is taken from the current thread,
    /// which libtest/nextest name after the test function.
    pub fn new(phase: &str) -> Self {
        let file = std::fs::File::create(format!("{}/{phase}.progress", test_log_dir())).ok();
        Self {
            file,
            last: Instant::now() - Self::INTERVAL,
        }
    }

    /// Appends a `status()` line if the rate limit allows (the closure only
    /// runs when a line is actually written).
    pub fn update(&mut self, status: impl FnOnce() -> String) {
        if self.last.elapsed() < Self::INTERVAL {
            return;
        }
        self.last = Instant::now();
        if let Some(file) = &mut self.file {
            let _ = writeln!(file, "{}", status());
        }
    }

    /// Appends the final `done:` line.
    pub fn finish(&mut self, status: impl std::fmt::Display) {
        if let Some(file) = &mut self.file {
            let _ = writeln!(file, "done: {status}");
        }
    }
}

/// Builds an observer for the `verify_configuration_*_observed` calls that
/// streams a live per-**node** utilisation breakdown to
/// `target/tmp/test-logs/<test>/<phase>.progress`. The flat per-worker step counts
/// are grouped into nodes of `cores_per_node` cores each (modelling a cluster of
/// `ceil(workers / cores_per_node)` nodes), and each line reports, per node, how
/// many of its cores were busy this wave and at what percentage - so you can watch
/// utilisation climb as the frontier fans out and fall away in the tail:
///
/// ```text
/// wave      6 | frontier               5,000 | cores 24/24 (100%) | node0 8/8 (100%) | node1 8/8 (100%)
/// wave     47 | frontier                   3 | cores  3/24 ( 12%) | node0 3/8 ( 37%) | node1 0/8 (  0%)
/// ```
///
/// One line per BFS wave (waves equal the BFS depth, which is small even when each
/// wave is huge). Every field is space-padded to a constant width so the line stays
/// aligned as the values change: `wave` to 6 digits, `frontier` to 15 comma-grouped
/// digits, each busy count to the width of its maximum, and the percent to 3. Big
/// counts are comma-grouped. Pass `Some(&observer)`; keep the returned value alive
/// across the verification call.
pub fn utilisation_log(phase: &str, cores_per_node: usize) -> impl Fn(&WaveReport) + Sync {
    let cores_per_node = cores_per_node.max(1);
    // A `Mutex` (not `RefCell`) so the observer is `Sync` and can cross into the
    // rayon pool's `install`; it is only ever called between waves, so it never
    // contends.
    let file = std::sync::Mutex::new(
        std::fs::File::create(format!("{}/{phase}.progress", test_log_dir())).ok(),
    );
    move |report: &WaveReport| {
        let pct = |busy: usize, total: usize| if total > 0 { 100 * busy / total } else { 0 };
        let total = report.units.len();
        let busy = report.units.iter().filter(|&&n| n > 0).count();
        // Constant-width fields: `frontier` for up to 15 comma-grouped digits (19
        // chars), `wave` for 6, and each current busy count right-padded to the
        // width of its maximum (total cores / a full node's cores).
        let total_width = total.separate_with_commas().len();
        let node_width = cores_per_node.separate_with_commas().len();
        let frontier = report.frontier.separate_with_commas();
        let busy_str = busy.separate_with_commas();
        let total_str = total.separate_with_commas();
        let mut line = format!(
            "wave {:>6} | frontier {frontier:>19} | cores {busy_str:>total_width$}/{total_str} ({:>3}%)",
            report.wave,
            pct(busy, total),
        );
        // Per node: how many of its cores stepped at least one continuation.
        for (node, cores) in report.units.chunks(cores_per_node).enumerate() {
            let n_busy = cores.iter().filter(|&&n| n > 0).count();
            let n_busy_str = n_busy.separate_with_commas();
            let n_total = cores.len();
            line.push_str(&format!(
                " | node{node} {n_busy_str:>node_width$}/{n_total} ({:>3}%)",
                pct(n_busy, n_total),
            ));
        }
        if let Ok(mut guard) = file.lock() {
            if let Some(handle) = guard.as_mut() {
                let _ = writeln!(handle, "{line}");
            }
        }
    }
}

/// Parses and compresses a dialect file given relative to `tests/` (each test
/// folder stores its own `dialect.s`, generated from its `input.hl` by
/// `hl::translate` and pinned by the test), returning the head of the AST.
///
/// The path is resolved against `CARGO_MANIFEST_DIR` so the tests do not depend
/// on the working directory.
pub fn setup_test(asset: &str) -> Option<NonNull<AstNode>> {
    let dir = env!("CARGO_MANIFEST_DIR");
    let path = std::path::PathBuf::from(format!("{dir}/tests/{asset}"));
    let source = std::fs::read_to_string(&path).unwrap();
    // `new_ast` splits lines on the *platform* newline (CRLF on Windows, LF on
    // Linux; see ast.rs). Normalize so a `dialect.s` with either line ending
    // parses regardless of how git checked it out: a no-op for a file that
    // already matches the platform.
    let unified = source.replace("\r\n", "\n");
    let source = if cfg!(windows) {
        unified.replace('\n', "\r\n")
    } else {
        unified
    };
    let chars = source.chars().collect::<Vec<_>>();
    let mut ast = new_ast(&chars, path);
    compress(&mut ast);
    ast
}

/// Inspects the leaf at the front of the queue, i.e. the `(hart, harts,
/// instruction)` that the *next* call to `next_step` will process. Returns
/// `None` only when the queue is empty (the next step yields `Valid`).
///
/// # Safety
/// `explorerer`'s verifier tree must be live.
pub unsafe fn front_step(explorerer: &Explorerer) -> Option<(u8, u8, String)> {
    let leaf = *explorerer.queue.front()?;
    let branch = (*leaf).prev;
    let node = (*branch).node;
    let hart = (*branch).hart;
    let harts = (*(*branch).root).configuration.harts;
    Some((hart, harts, node.as_ref().value.this.to_string()))
}

/// Drives the explorer to a terminal state, recording one exact trace line per
/// `next_step` so a test can pin the *incremental* behaviour of the state
/// machine. Each line is:
///
/// ```text
/// h<hart>/<harts> | <instruction> | <config> | q<queue> t<touched> j<jumped>
/// ```
///
/// where `<hart>` is the (0-based) hart whose `<instruction>` is being processed
/// this step and `<config>`/`q`/`t`/`j` are the resulting `configuration`,
/// queue length, `touched` count and `jumped` count *after* the step. Because
/// the trace records every step (including the type-search backtracking), any
/// change in exploration order, type inference, racy interleaving or
/// optimization accounting will alter it, which is exactly the regression
/// signal these tests exist to provide.
///
/// Returns the trace together with the terminal result of exploration: `Ok` of
/// the terminal [`ExplorePathResult`] (`Valid` / `Invalid`), or `Err` of the
/// [`CompilerError`] the verifier hit. The trace is returned in **all** cases,
/// including on error, so a test can report where the error occurred. Use
/// [`expect_valid`] to assert success.
///
/// # Safety
/// `explorerer` must have been constructed from a live AST that outlives this
/// call (see [`Explorerer::new`]).
pub unsafe fn trace_valid_path(
    mut explorerer: Explorerer,
) -> (Vec<String>, Result<ExplorePathResult, CompilerError>) {
    const STEP_CAP: usize = 10_000_000;
    let mut trace = Vec::new();
    // Live progress (the verifier can take millions of steps) streams to
    // `target/tmp/test-logs/<test>/verify.progress`, never to the console (see
    // [`Progress`]).
    let mut progress = Progress::new("verify");
    for step in 0..STEP_CAP {
        progress.update(|| {
            format!(
                "step {} (queue {})",
                step.separate_with_commas(),
                explorerer.queue.len().separate_with_commas()
            )
        });
        let pre = front_step(&explorerer);
        match explorerer.next_step() {
            Ok(ExplorePathResult::Continue(next)) => {
                explorerer = next;
                let (hart, harts, instruction) = pre.expect("Continue step with an empty queue");
                trace.push(format!(
                    "h{hart}/{harts} | {instruction} | {} | q{} t{} j{}",
                    explorerer.configuration,
                    explorerer.queue.len(),
                    explorerer.touched.len(),
                    explorerer.jumped.len(),
                ));
            }
            // `Valid` / `Invalid` are terminal outcomes; an `Err` is an unrecoverable
            // compiler error. Either way return it with the trace collected so far so
            // the test can inspect both.
            Ok(terminal) => {
                progress.finish(format_args!("{} steps", trace.len()));
                dump_trace(&trace);
                return (trace, Ok(terminal));
            }
            Err(error) => {
                // Record the step that failed (and the error) as the final trace line so
                // the trace shows *where* the error occurred.
                if let Some((hart, harts, instruction)) = pre {
                    trace.push(format!(
                        "h{hart}/{harts} | {instruction} | <error: {error}>"
                    ));
                }
                progress.finish(format_args!("error after {} steps", trace.len()));
                dump_trace(&trace);
                return (trace, Err(error));
            }
        }
    }
    progress.finish("step cap exceeded");
    panic!("exploration did not terminate within {STEP_CAP} steps");
}

/// Re-baseline mode: true when `BLESS` is set in the environment. In this mode
/// the brittle pins that legitimately change with behaviour are regenerated
/// from actual output in a single run rather than asserted: [`bless_asm`]
/// overwrites each golden `.s`, [`trace_valid_path`] dumps the trace and step
/// count to `target/tmp`, and a test skips its inline trace/step-count
/// assertions (see the `if !blessing()` guards in the tests). The QEMU boot
/// still runs, so a blessed program is still proven to execute. Re-baseline
/// **deliberately**: inspect the regenerated pins and re-derive the inline
/// expectations from the dumped trace; never bless to paper over a regression.
pub fn blessing() -> bool {
    std::env::var_os("BLESS").is_some()
}

/// Pins `actual` against the golden file `tests/<rel>`: asserts equality
/// (line-ending-normalized) in a normal run, or, in [`blessing`] mode,
/// overwrites the golden with `actual` and returns without asserting.
/// `included` is the compile-time contents of the same file (`include_str!`),
/// compared so the golden gets assembly syntax highlighting as a file.
pub fn bless_asm(rel: &str, actual: String, included: &str) {
    if blessing() {
        let path = format!("{}/tests/{}", env!("CARGO_MANIFEST_DIR"), rel);
        std::fs::write(&path, actual.as_bytes()).expect("bless write failed");
        return;
    }
    assert_eq!(
        normalize(actual),
        normalize(included),
        "golden mismatch: {rel}"
    );
}

/// In [`blessing`] mode writes the trace and its step count to
/// `target/tmp/test-logs/<test>/trace` and `.../meta` so re-baselining a pinned
/// trace, step count, or configuration timeline starts from the actual
/// behaviour. A no-op in a normal run. Very long traces (e.g. `uart_hello`'s ~2M
/// steps) write only the `meta` count, not the full trace.
fn dump_trace(trace: &[String]) {
    if !blessing() {
        return;
    }
    let dir = test_log_dir();
    let _ = std::fs::write(format!("{dir}/meta"), format!("steps={}\n", trace.len()));
    if trace.len() <= 100_000 {
        let _ = std::fs::write(format!("{dir}/trace"), trace.join("\n"));
    }
}

/// Asserts the verifier reached a valid path and returns it. On any other
/// outcome (`Invalid`, or a [`CompilerError`]) it panics with the outcome and
/// the tail of the trace, so a regression shows *where* exploration went wrong.
pub fn expect_valid(
    trace: &[String],
    result: Result<ExplorePathResult, CompilerError>,
) -> ValidPathResult {
    match result {
        Ok(ExplorePathResult::Valid(valid)) => valid,
        other => {
            let tail = trace
                .iter()
                .enumerate()
                .skip(trace.len().saturating_sub(8))
                .map(|(i, l)| format!("  {i}: {l}"))
                .collect::<Vec<_>>()
                .join("\n");
            panic!(
                "expected a valid path, got {other:?}\nlast {} step(s):\n{tail}",
                trace.len().min(8)
            );
        }
    }
}

/// Normalizes line endings so the expected strings (written with `\n`) compare
/// equal regardless of the platform-specific line ending emitted by
/// [`print_ast`] (which uses `\r\n` on Windows).
pub fn normalize(s: impl Into<String>) -> String {
    s.into().replace("\r\n", "\n")
}

/// The result of building and booting a generated program in QEMU.
pub struct QemuOutcome {
    /// Bytes the program wrote to the UART (the QEMU `virt` 16550 at 0x10000000).
    pub serial: String,
    /// Number of guest CPU exceptions/faults QEMU logged; `0` means it ran cleanly.
    pub faults: usize,
    /// The head of QEMU's `guest_errors` log (for diagnostics on failure).
    pub fault_log: String,
}

fn between<'a>(s: &'a str, begin: &str, end: &str) -> &'a str {
    s.split_once(begin)
        .and_then(|(_, rest)| rest.split_once(end))
        .map(|(mid, _)| mid)
        .unwrap_or("")
}

/// Writes the generated program `asm` to `target/gen/<name>.s`, then, under WSL,
/// assembles + links it with the RISC-V GNU toolchain and boots it in
/// `qemu-system-riscv64 -machine virt`, returning the captured UART output and
/// CPU-fault count.
///
/// **The toolchain and QEMU are required**: this panics (failing the test) if WSL,
/// the RISC-V GNU toolchain, or `qemu-system-riscv64` are unavailable, or if
/// assembling/linking the generated program fails. The tests are meant to verify
/// the output actually boots, so a missing toolchain is a failure, not a skip.
///
/// The toolchain `bin/` directory defaults to `$HOME/riscv-toolchain/riscv/bin`
/// (a stable [riscv-gnu-toolchain] release extracted into WSL) and can be
/// overridden with the `RISCV_BIN` environment variable.
///
/// [riscv-gnu-toolchain]: https://github.com/riscv-collab/riscv-gnu-toolchain/releases
pub fn run_in_qemu(name: &str, asm: &str, smp: u8) -> QemuOutcome {
    run_in_qemu_opts(name, asm, smp, false)
}

/// Like [`run_in_qemu`] but, with `long = true`, runs a long compute (e.g. a large
/// fannkuch n) to completion: normal TCG (not `one-insn-per-tb`) and no
/// per-instruction `exec` logging -- both of which would make 479M instructions
/// take hours and produce an astronomically large log -- and a long timeout.
/// Fault detection (`guest_errors`) is kept.
pub fn run_in_qemu_opts(name: &str, asm: &str, smp: u8, long: bool) -> QemuOutcome {
    let (timeout, accel, logd) = if long {
        // `thread=multi` (MTTCG) runs each hart on its own host core, so the
        // leader gets a full core instead of round-robin time-slicing against the
        // parked workers.
        ("420", "tcg,thread=multi", "guest_errors")
    } else {
        ("3", "tcg,one-insn-per-tb=on", "guest_errors,exec,nochain")
    };
    use std::process::Command;

    let dir = env!("CARGO_MANIFEST_DIR");
    let gen = format!("{dir}/target/gen");
    std::fs::create_dir_all(&gen).expect("create target/gen");
    std::fs::write(format!("{gen}/{name}.s"), asm).expect("write generated .s");

    let bin = std::env::var("RISCV_BIN")
        .unwrap_or_else(|_| "$HOME/riscv-toolchain/riscv/bin".to_string());
    // `--no-relax`: keep `la` PC-relative; a bare-metal program has no `gp`. The
    // program halts in a `wfi` loop, so `timeout` bounds the run; the UART output
    // is captured to a file and the CPU faults to the `guest_errors` log.
    let script = format!(
        r#"set -e
BIN="{bin}"
AS="$BIN/riscv64-unknown-elf-as"
LD="$BIN/riscv64-unknown-elf-ld"
command -v qemu-system-riscv64 >/dev/null 2>&1 || {{ echo "===MISSING===qemu-system-riscv64 is not on the WSL PATH (install QEMU in WSL)"; exit 0; }}
{{ [ -x "$AS" ] && [ -x "$LD" ]; }} || {{ echo "===MISSING===the RISC-V toolchain (riscv64-unknown-elf-as/ld) was not found at $BIN (set RISCV_BIN, or extract a riscv-gnu-toolchain release there)"; exit 0; }}
G="$(wslpath '{gen}')"
"$AS" -o "$G/{name}.o" "$G/{name}.s"
"$LD" -Ttext=0x80000000 --no-relax -e _start -o "$G/{name}.elf" "$G/{name}.o"
rm -f "$G/{name}.serial" "$G/{name}.qemu.log"
# `one-insn-per-tb` + `-d exec,nochain` log one line per *executed instruction*
# (to stderr, which is unbuffered, so the host can watch the count live for
# progress reporting); `guest_errors` shares the same log for fault detection.
timeout {timeout} qemu-system-riscv64 -machine virt -smp {smp} -bios none -display none -monitor none \
    -accel {accel} -d {logd} \
    -serial "file:$G/{name}.serial" -kernel "$G/{name}.elf" \
    >/dev/null 2>"$G/{name}.qemu.log" || true
echo "===SERIAL_BEGIN==="
cat "$G/{name}.serial" 2>/dev/null
echo ""
echo "===SERIAL_END==="
FAULTS="$(grep -c riscv_cpu_do_interrupt "$G/{name}.qemu.log" 2>/dev/null || true)"
echo "===FAULTS===${{FAULTS:-0}}"
echo "===LOG==="
grep -v '^Trace' "$G/{name}.qemu.log" 2>/dev/null | head -c 2000 || true
echo ""
echo "===END==="
"#
    );

    // Run the (multi-second: QEMU runs under a fixed timeout) build+boot on a
    // worker thread and report live progress meanwhile: elapsed time plus the
    // number of guest instructions executed so far, read from the exec log QEMU
    // writes as it runs.
    let worker = {
        let script = script.clone();
        std::thread::spawn(move || {
            let mut command = Command::new("wsl");
            command.arg("-e").arg("bash").arg("-lc").arg(&script);
            // Detach WSL from our console (`CREATE_NO_WINDOW`). `wsl.exe`
            // mutates the console mode of whatever console it attaches to,
            // which corrupts the test runner's output for the rest of the run
            // (newlines stop carriage-returning, the "staircase" effect, and
            // in-place progress displays print a new line per redraw). Its
            // output is piped by `.output()`, so it never needs the console.
            #[cfg(windows)]
            {
                use std::os::windows::process::CommandExt;
                const CREATE_NO_WINDOW: u32 = 0x0800_0000;
                command.creation_flags(CREATE_NO_WINDOW);
            }
            command.output()
        })
    };
    // Progress (elapsed time + live guest instruction count, read from the exec
    // log QEMU writes as it runs) streams to `target/tmp/<test>.qemu.progress`.
    let mut progress = Progress::new("qemu");
    let log_path = format!("{gen}/{name}.qemu.log");
    let started = Instant::now();
    while !worker.is_finished() {
        progress.update(|| {
            let instructions = std::fs::read_to_string(&log_path)
                .map(|log| log.lines().filter(|l| l.starts_with("Trace")).count())
                .unwrap_or(0);
            format!(
                "{:.1}s, {instructions} instructions executed",
                started.elapsed().as_secs_f32()
            )
        });
        std::thread::sleep(Duration::from_millis(50));
    }
    progress.finish(format_args!(
        "booted in {:.1}s",
        started.elapsed().as_secs_f32()
    ));
    let output = worker
        .join()
        .expect("the WSL worker thread panicked")
        .expect(
            "failed to invoke WSL: WSL with the RISC-V GNU toolchain and \
             qemu-system-riscv64 is required to build and boot the generated program",
        );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if let Some((_, rest)) = stdout.split_once("===MISSING===") {
        let reason = rest.lines().next().unwrap_or("").trim();
        panic!(
            "`{name}`: cannot build/boot the generated program ({reason}).\n\
             QEMU (`qemu-system-riscv64`) and the RISC-V GNU toolchain are REQUIRED to \
             run these tests; install them under WSL (point `RISCV_BIN` at the toolchain \
             `bin/`)."
        );
    }
    assert!(
        stdout.contains("===END==="),
        "assembling/linking the generated `{name}` program failed:\n\
         --- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
    );

    let serial = between(&stdout, "===SERIAL_BEGIN===", "===SERIAL_END===")
        .trim_matches('\n')
        .to_string();
    let faults = between(&stdout, "===FAULTS===", "===LOG===")
        .trim()
        .parse()
        .unwrap_or(usize::MAX);
    let fault_log = between(&stdout, "===LOG===", "===END===")
        .trim()
        .to_string();

    QemuOutcome {
        serial,
        faults,
        fault_log,
    }
}

/// Lowers the verified + optimized program to runnable RISC-V (`emit_executable`),
/// checks it is self-contained (entry, halt loop, storage for every inferred
/// variable) and that **no compile-time-only data leaked into it**, then builds
/// and boots it in QEMU, asserting it ran **without any CPU fault**, and returns
/// the captured UART output for the caller to assert on.
///
/// Requires the toolchain + QEMU (see [`run_in_qemu`]); panics if they are absent.
///
/// # Safety
/// `ast` must be a live AST (typically the optimized output of the pipeline).
pub unsafe fn run_program(
    name: &str,
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned_nodes: &BTreeSet<NonNull<AstNode>>,
) -> String {
    run_program_smp(
        name,
        1,
        false,
        ast,
        configuration,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    )
}

/// Like [`run_program`] but boots `harts` harts (`qemu -smp harts`): for a
/// genuinely multi-threaded program whose harts must all run (work-claiming
/// atomics, a last-finisher barrier), not just a leader. The verified hart count
/// and the booted hart count then match. `long = true` uses the long-compute QEMU
/// config (see [`run_in_qemu_opts`]) for a large fannkuch n.
#[allow(clippy::too_many_arguments)]
pub unsafe fn run_program_smp(
    name: &str,
    harts: u8,
    long: bool,
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned_nodes: &BTreeSet<NonNull<AstNode>>,
) -> String {
    let asm = emit_executable(
        ast,
        configuration,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    );

    // The emitted program must be self-contained.
    assert!(
        asm.contains(".global _start"),
        "{name}: no entry point\n{asm}"
    );
    assert!(asm.contains("__halt:"), "{name}: no halt loop\n{asm}");
    for label in configuration.0.keys() {
        assert!(
            asm.contains(&format!("{label}:")),
            "{name}: no generated storage for `{label}`\n{asm}"
        );
    }

    // Dead-data elimination: information only read at *compile time* (by the
    // verifier) must not be stored in the output. None of these programs read a
    // descriptor's locality byte at runtime, so no locality data (the only
    // `.byte` directives the descriptor emitter produces) may survive anywhere
    // in the generated `.data`/`.bss` sections.
    if let Some((_, generated_sections)) = asm.split_once(".section .data") {
        assert!(
            !generated_sections.contains(".byte"),
            "{name}: compile-time-only locality data leaked into the output:\n{asm}"
        );
    }

    let outcome = run_in_qemu_opts(name, &asm, harts, long);
    assert_eq!(
        outcome.faults, 0,
        "{name}: program faulted in QEMU ({} CPU exception(s)):\n{}",
        outcome.faults, outcome.fault_log
    );
    outcome.serial
}

/// Like [`run_in_qemu`], but builds and runs a **Linux** RISC-V program rather
/// than booting bare metal: it assembles + links a static ELF (entry `_start`,
/// no fixed text address) and runs it under the user-mode emulator
/// `qemu-riscv64` (bundled in the toolchain `bin/`), returning what the program
/// wrote to standard output. This is how `linux_hello` exercises the std
/// library's `print`, which issues the Linux `write`/`exit` system calls via
/// `ecall`.
///
/// Requires the RISC-V GNU toolchain and `qemu-riscv64`; like [`run_in_qemu`] it
/// panics (failing the test) if they are missing, rather than skipping.
pub fn run_linux(name: &str, asm: &str) -> String {
    use std::process::Command;

    let dir = env!("CARGO_MANIFEST_DIR");
    let gen = format!("{dir}/target/gen");
    std::fs::create_dir_all(&gen).expect("create target/gen");
    std::fs::write(format!("{gen}/{name}.s"), asm).expect("write generated .s");

    let bin = std::env::var("RISCV_BIN")
        .unwrap_or_else(|_| "$HOME/riscv-toolchain/riscv/bin".to_string());
    let script = format!(
        r#"set -e
BIN="{bin}"
AS="$BIN/riscv64-unknown-elf-as"
LD="$BIN/riscv64-unknown-elf-ld"
QEMU="$BIN/qemu-riscv64"
{{ [ -x "$AS" ] && [ -x "$LD" ] && [ -x "$QEMU" ]; }} || {{ echo "===MISSING===the RISC-V toolchain (as/ld) and user-mode qemu-riscv64 were not found under $BIN (set RISCV_BIN)"; exit 0; }}
G="$(wslpath '{gen}')"
"$AS" -o "$G/{name}.o" "$G/{name}.s"
# Static ELF with entry `_start`; `--no-relax` keeps `la` PC-relative (no `gp`).
"$LD" --no-relax -e _start -o "$G/{name}.elf" "$G/{name}.o"
echo "===OUT_BEGIN==="
timeout 150 "$QEMU" "$G/{name}.elf" || true
echo "===OUT_END==="
echo "===END==="
"#
    );

    let worker = {
        let script = script.clone();
        std::thread::spawn(move || {
            let mut command = Command::new("wsl");
            command.arg("-e").arg("bash").arg("-lc").arg(&script);
            // Detach WSL from the console (see the note in `run_in_qemu`).
            #[cfg(windows)]
            {
                use std::os::windows::process::CommandExt;
                const CREATE_NO_WINDOW: u32 = 0x0800_0000;
                command.creation_flags(CREATE_NO_WINDOW);
            }
            command.output()
        })
    };
    let mut progress = Progress::new("qemu");
    let started = Instant::now();
    while !worker.is_finished() {
        progress.update(|| {
            format!(
                "{:.1}s building + running under qemu-riscv64",
                started.elapsed().as_secs_f32()
            )
        });
        std::thread::sleep(Duration::from_millis(50));
    }
    progress.finish(format_args!(
        "ran in {:.1}s",
        started.elapsed().as_secs_f32()
    ));
    let output = worker
        .join()
        .expect("the WSL worker thread panicked")
        .expect(
            "failed to invoke WSL: WSL with the RISC-V GNU toolchain and qemu-riscv64 is \
         required to build and run the generated Linux program",
        );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if let Some((_, rest)) = stdout.split_once("===MISSING===") {
        let reason = rest.lines().next().unwrap_or("").trim();
        panic!(
            "`{name}`: cannot build/run the Linux program ({reason}). The RISC-V GNU \
             toolchain and `qemu-riscv64` are REQUIRED; install them under WSL (point \
             `RISCV_BIN` at the toolchain `bin/`)."
        );
    }
    assert!(
        stdout.contains("===END==="),
        "assembling/linking/running the Linux `{name}` program failed:\n\
         --- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
    );
    between(&stdout, "===OUT_BEGIN===", "===OUT_END===")
        .trim_matches('\n')
        .to_string()
}

/// Extracts the sequence of distinct, consecutive `configuration` strings from a
/// [`trace_valid_path`] trace, i.e. the type-inference timeline. A reset to
/// `Config: []` marks a backtrack to re-try a variable's next candidate type.
pub fn config_timeline(trace: &[String]) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    for line in trace {
        if let Some(config) = line.split(" | ").nth(2) {
            if out.last().map(String::as_str) != Some(config) {
                out.push(config.to_string());
            }
        }
    }
    out
}

/// Asserts a live trace matches `expected` line for line, reporting the first
/// diverging step index (and then any length difference). Far more debuggable
/// than a single `assert_eq!` over the whole vector.
pub fn assert_trace(actual: &[String], expected: &[&str]) {
    for (i, (got, want)) in actual.iter().zip(expected.iter()).enumerate() {
        assert_eq!(got, want, "trace diverged at step {i}");
    }
    assert_eq!(
        actual.len(),
        expected.len(),
        "trace length differs (first {} steps matched)",
        actual.len().min(expected.len())
    );
}

// ---------------------------------------------------------------------------
// Model switch: verify a program either with the simple in-process (sequential)
// model or the distributed HPC (MPI) model, with one reusable call.
// ---------------------------------------------------------------------------

/// Which model to verify a program under.
///
/// A test picks a default; it can be overridden **before running**, without
/// editing the test, via the `FORMAL_TEST_MODEL` environment variable:
/// `sequential` (or `seq`), `hpc`, or `hpc:<ranks>` (e.g. `hpc:16`). So
/// `FORMAL_TEST_MODEL=sequential cargo nt hpc_demo` runs the same test in-process.
#[derive(Clone, Copy, Debug)]
pub enum Model {
    /// In-process on one machine, no MPI: the simple reference model
    /// ([`verify_inferred`]).
    Sequential,
    /// Distributed across `ranks` MPI processes via `mpirun` (needs WSL + the
    /// `--features hpc` build, built once into `~/formal-hpc`).
    Hpc { ranks: usize },
}

/// The normalised result of verifying a program under a [`Model`]: the inferred
/// configuration and accessed byte-ranges as their canonical `Display`/`Debug`
/// strings (so the two models are directly comparable), the touched-node count,
/// and the path of the detail log written under `target/tmp/test-logs/<test>/`.
pub struct ModelOutcome {
    pub model: String,
    pub configuration: String,
    pub accessed: String,
    pub touched: usize,
    pub log: String,
}

/// Applies any `FORMAL_TEST_MODEL` override to `default`.
fn resolve_model(default: Model) -> Model {
    match std::env::var("FORMAL_TEST_MODEL").ok().as_deref() {
        Some("sequential") | Some("seq") => Model::Sequential,
        Some(hpc) if hpc == "hpc" || hpc.starts_with("hpc:") => {
            let ranks = hpc
                .strip_prefix("hpc:")
                .and_then(|r| r.trim().parse().ok())
                .unwrap_or(match default {
                    Model::Hpc { ranks } => ranks,
                    Model::Sequential => 8,
                });
            Model::Hpc { ranks }
        }
        _ => default,
    }
}

/// Builds the `--features hpc` binary in WSL (cached in `~/formal-hpc`) and runs
/// `formal <args>` under `mpirun -n ranks`, returning the merged stdout.
///
/// Requires WSL + a system MPI; like [`run_in_qemu`] it **panics** (failing the
/// test) if they are absent, rather than skipping.
pub fn mpirun_formal(ranks: usize, args: &str) -> String {
    use std::process::Command;
    let dir = env!("CARGO_MANIFEST_DIR");
    let script = format!(
        "set -e\n\
         cd \"$(wslpath '{dir}')\"\n\
         FORMAL_NO_SETUP=1 ~/.cargo/bin/cargo build --features hpc --bin formal \
            --target-dir ~/formal-hpc >/dev/null 2>&1\n\
         mpirun --mca mpi_yield_when_idle 1 --oversubscribe -n {ranks} \
            ~/formal-hpc/debug/formal {args}"
    );
    let mut command = Command::new("wsl");
    command.args(["-e", "bash", "-lc", &script]);
    // Detach WSL from the console (see the note in `run_in_qemu`).
    #[cfg(windows)]
    {
        use std::os::windows::process::CommandExt;
        const CREATE_NO_WINDOW: u32 = 0x0800_0000;
        command.creation_flags(CREATE_NO_WINDOW);
    }
    let output = command.output().expect(
        "failed to invoke WSL: WSL with a system MPI (mpirun) and the `--features hpc` build \
         dependencies is REQUIRED to run the HPC model",
    );
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    assert!(
        output.status.success(),
        "wsl build/mpirun failed (`formal {args}`, {ranks} rank(s)):\n--- stdout ---\n{stdout}\n\
         --- stderr ---\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    stdout
}

/// Verifies the dialect program `asset` (relative to `tests/`) under `default`
/// model (overridable via `FORMAL_TEST_MODEL`), writing a detail log under
/// `target/tmp/test-logs/<test>/`. `harts` lists the systems to verify under (one
/// per hart count, e.g. `&[1, 2]`). Returns the normalised [`ModelOutcome`] so a
/// test asserts on the inferred configuration / accessed ranges regardless of
/// which model actually ran.
///
/// - `Sequential`: in-process [`verify_inferred`]; writes `sequential.log`.
/// - `Hpc`: shells out to `mpirun … formal mpi-verify`, which streams per-rank
///   progress + a utilisation breakdown; the full output is saved to `hpc.log`.
pub fn verify_with_model(asset: &str, harts: &[u8], default: Model) -> ModelOutcome {
    let dir = test_log_dir();
    match resolve_model(default) {
        Model::Sequential => {
            let ast = setup_test(asset);
            let systems: Vec<InnerVerifierConfiguration> = harts
                .iter()
                .map(|&harts| InnerVerifierConfiguration {
                    sections: Default::default(),
                    harts,
                })
                .collect();
            let result = unsafe { verify_inferred(ast, &systems) }
                .expect("sequential verify_inferred failed");
            let valid = match result {
                ExplorePathResult::Valid(valid) => valid,
                _ => panic!("{asset}: the sequential model did not reach a valid configuration"),
            };
            let configuration = format!("{}", valid.configuration);
            let accessed = normalize(format!("{:?}", valid.accessed));
            let touched = valid.touched.len();
            let log = format!("{dir}/sequential.log");
            let _ = std::fs::write(
                &log,
                format!(
                    "model = sequential (in-process)\nprogram = tests/{asset}\nsystems = {harts:?}\n\
                     configuration = {configuration}\ntouched = {touched}\naccessed = {accessed}\n"
                ),
            );
            ModelOutcome {
                model: "sequential".into(),
                configuration,
                accessed,
                touched,
                log,
            }
        }
        Model::Hpc { ranks } => {
            let harts_csv = harts
                .iter()
                .map(u8::to_string)
                .collect::<Vec<_>>()
                .join(",");
            let out = mpirun_formal(ranks, &format!("mpi-verify tests/{asset} {harts_csv}"));
            let log = format!("{dir}/hpc.log");
            let _ = std::fs::write(&log, &out);
            let line = out
                .lines()
                .find(|l| l.starts_with("[mpi-verify] ranks="))
                .unwrap_or_else(|| {
                    panic!("{asset}: no `[mpi-verify]` result line in the HPC output (see {log})\n{out}")
                });
            let configuration = between(line, "config=", " touched=").trim().to_string();
            let touched = between(line, "touched=", " accessed=")
                .trim()
                .parse()
                .unwrap_or(0);
            let accessed = normalize(
                line.split_once("accessed=")
                    .map(|(_, a)| a)
                    .unwrap_or("")
                    .to_string(),
            );
            ModelOutcome {
                model: format!("hpc ({ranks} ranks)"),
                configuration,
                accessed,
                touched,
                log,
            }
        }
    }
}
