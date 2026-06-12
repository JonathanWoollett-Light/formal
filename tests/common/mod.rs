//! Shared helpers for the integration tests.
//!
//! Each test binary in `tests/` includes this module via `mod common;`, so some
//! helpers appear unused from any single test binary's perspective.
#![allow(dead_code)]

use formal::verifier_types::TypeConfiguration;
use formal::*;
use std::ptr::NonNull;

/// Parses and compresses `assets/<asm>.s`, returning the head of the AST.
///
/// The path is resolved against `CARGO_MANIFEST_DIR` so the tests do not depend
/// on the working directory.
pub fn setup_test(asm: &str) -> Option<NonNull<AstNode>> {
    let dir = env!("CARGO_MANIFEST_DIR");
    let path = std::path::PathBuf::from(format!("{dir}/assets/{asm}.s"));
    let source = std::fs::read_to_string(&path).unwrap();
    let chars = source.chars().collect::<Vec<_>>();
    let mut ast = new_ast(&chars, path);
    compress(&mut ast);
    ast
}

/// Inspects the leaf at the front of the queue — i.e. the `(hart, harts,
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
/// optimization accounting will alter it — which is exactly the regression
/// signal these tests exist to provide.
///
/// Returns the trace together with the terminal result of exploration: `Ok` of
/// the terminal [`ExplorePathResult`] (`Valid` / `Invalid`), or `Err` of the
/// [`CompilerError`] the verifier hit. The trace is returned in **all** cases —
/// including on error — so a test can report where the error occurred. Use
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
    for _ in 0..STEP_CAP {
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
            Ok(terminal) => return (trace, Ok(terminal)),
            Err(error) => {
                // Record the step that failed (and the error) as the final trace line so
                // the trace shows *where* the error occurred.
                if let Some((hart, harts, instruction)) = pre {
                    trace.push(format!("h{hart}/{harts} | {instruction} | <error: {error}>"));
                }
                return (trace, Err(error));
            }
        }
    }
    panic!("exploration did not terminate within {STEP_CAP} steps");
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

/// Runs the full pipeline for `name` — parse, compress, verify (over the given
/// hart counts), then `remove_untouched` + `remove_branches` — and returns the
/// optimized AST plus the inferred `TypeConfiguration`. Panics if verification
/// does not reach a valid path.
///
/// # Safety
/// As [`Explorerer::new`] / the optimizer: operates on the raw-pointer AST.
pub unsafe fn verify_and_optimize(
    name: &str,
    sections: Vec<Section>,
    harts: &[u8],
) -> (Option<NonNull<AstNode>>, TypeConfiguration) {
    let mut ast = setup_test(name);
    let systems = harts
        .iter()
        .map(|&harts| InnerVerifierConfiguration {
            sections: sections.clone(),
            harts,
        })
        .collect::<Vec<_>>();
    let explorerer = Explorerer::new(ast, &systems).expect("failed to construct the verifier");
    let (trace, result) = trace_valid_path(explorerer);
    let ValidPathResult {
        configuration,
        touched,
        jumped,
    } = expect_valid(&trace, result);
    remove_untouched(&mut ast, &touched);
    remove_branches(&mut ast, &jumped);
    (ast, configuration)
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
    /// Number of guest CPU exceptions/faults QEMU logged — `0` means it ran cleanly.
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

/// Writes the generated program `asm` to `target/gen/<name>.s`, then — under WSL —
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
pub fn run_in_qemu(name: &str, asm: &str) -> QemuOutcome {
    use std::process::Command;

    let dir = env!("CARGO_MANIFEST_DIR");
    let gen = format!("{dir}/target/gen");
    std::fs::create_dir_all(&gen).expect("create target/gen");
    std::fs::write(format!("{gen}/{name}.s"), asm).expect("write generated .s");

    let bin = std::env::var("RISCV_BIN").unwrap_or_else(|_| "$HOME/riscv-toolchain/riscv/bin".to_string());
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
timeout 3 qemu-system-riscv64 -machine virt -bios none -display none -monitor none \
    -serial "file:$G/{name}.serial" -kernel "$G/{name}.elf" \
    -d guest_errors -D "$G/{name}.qemu.log" >/dev/null 2>&1 || true
echo "===SERIAL_BEGIN==="
cat "$G/{name}.serial" 2>/dev/null
echo ""
echo "===SERIAL_END==="
FAULTS="$(grep -c riscv_cpu_do_interrupt "$G/{name}.qemu.log" 2>/dev/null || true)"
echo "===FAULTS===${{FAULTS:-0}}"
echo "===LOG==="
head -c 2000 "$G/{name}.qemu.log" 2>/dev/null || true
echo ""
echo "===END==="
"#
    );

    let output = Command::new("wsl")
        .arg("-e")
        .arg("bash")
        .arg("-lc")
        .arg(&script)
        .output()
        .expect(
            "failed to invoke WSL — WSL with the RISC-V GNU toolchain and \
             qemu-system-riscv64 is required to build and boot the generated program",
        );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);

    if let Some((_, rest)) = stdout.split_once("===MISSING===") {
        let reason = rest.lines().next().unwrap_or("").trim();
        panic!(
            "`{name}`: cannot build/boot the generated program — {reason}.\n\
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
    let fault_log = between(&stdout, "===LOG===", "===END===").trim().to_string();

    QemuOutcome {
        serial,
        faults,
        fault_log,
    }
}

/// Lowers the verified + optimized program to runnable RISC-V (`emit_executable`),
/// checks it is self-contained (entry, halt loop, storage for every inferred
/// variable), then builds and boots it in QEMU, asserting it ran **without any CPU
/// fault**, and returns the captured UART output for the caller to assert on.
///
/// Requires the toolchain + QEMU (see [`run_in_qemu`]); panics if they are absent.
///
/// # Safety
/// `ast` must be a live AST (typically the optimized output of the pipeline).
pub unsafe fn run_program(
    name: &str,
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
) -> String {
    let asm = emit_executable(ast, configuration);

    // The emitted program must be self-contained.
    assert!(asm.contains(".global _start"), "{name}: no entry point\n{asm}");
    assert!(asm.contains("__halt:"), "{name}: no halt loop\n{asm}");
    for label in configuration.0.keys() {
        assert!(
            asm.contains(&format!("{label}:")),
            "{name}: no generated storage for `{label}`\n{asm}"
        );
    }

    let outcome = run_in_qemu(name, &asm);
    assert_eq!(
        outcome.faults, 0,
        "{name}: program faulted in QEMU ({} CPU exception(s)):\n{}",
        outcome.faults, outcome.fault_log
    );
    outcome.serial
}

/// Extracts the sequence of distinct, consecutive `configuration` strings from a
/// [`trace_valid_path`] trace — i.e. the type-inference timeline. A reset to
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
