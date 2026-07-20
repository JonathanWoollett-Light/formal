#[path = "../common/mod.rs"]
mod common;
mod support;

use common::*;
use formal::*;
use std::fs;
use std::time::Instant;
use support::*;

/// **The language-comparison metrics pipeline** behind the website's
/// "The same program, side by side" panels.
///
/// For each comparison program (`hello`, `fannkuch`) x language (`formal`,
/// `rust`, `c`, `cpp`, `zig`, `ada`), this test builds the program under
/// **controlled, pinned conditions** (a static RISC-V Linux binary per
/// language's pinned toolchain; Ada is host-static, build-only) and measures:
///
/// - `compile_seconds`: wall-clock build time (cold output dir, warm caches),
/// - `static_instructions`: machine instructions in the binary (formal: lines
///   of emitted assembly, the others: `objdump` of the stripped binary),
/// - `binary_bytes`: the stripped static executable's size,
/// - `executed_instructions` / `peak_memory_kib`: exact guest instruction count
///   and peak working set from an instrumented (`formal_stats` TCG plugin) run
///   under user-mode `qemu-riscv64` with an **empty guest environment**,
/// - `run_seconds`: a separate plugin-free timed run (best of 3 for `hello`).
///
/// The results live in `tests/comparisons/metrics.prom` (Prometheus text
/// format), which works like `Cargo.lock`: **committed, but generated**.
/// Modes:
///
/// - **Normal (check)**: re-measures every language whose pinned toolchain is
///   present at the *recorded* version (see the environment-info metric in the
///   file) and asserts the deterministic metrics reproduce the committed
///   values exactly - timings are informational, and formal's 2-thread
///   fannkuch instruction count gets a 10% tolerance (real scheduling
///   nondeterminism). Values still marked `origin="legacy"` (imported from the
///   pre-pipeline experiment) only warn. Also asserts `index.html` is in sync
///   with the committed file. Missing/mismatched toolchains skip with a
///   warning, or fail under `FORMAL_COMPARISONS_STRICT=1` (CI).
/// - **`BLESS=1` (measure)**: rewrites the measured entries (flipping them to
///   `origin="measured"`), records the environment, regenerates the file AND
///   re-injects the numbers into `index.html`.
///
/// `FORMAL_COMPARISONS_FULL=1` adds the heavy fannkuch-redux *runtime* runs
/// (n = 12: minutes uninstrumented, potentially hours instrumented); without
/// it fannkuch is built and measured statically only, and its committed
/// runtime figures are left untouched.
///
/// Run it explicitly (it is `#[ignore]`d out of the default suite):
/// `cargo nextest run --run-ignored all comparisons`.
#[test]
#[ignore = "measures the website's language comparisons; needs the pinned toolchains (DEVELOPMENT.md)"]
fn comparisons() {
    let manifest = env!("CARGO_MANIFEST_DIR");
    let metrics_path = format!("{manifest}/tests/comparisons/metrics.prom");
    let html_path = format!("{manifest}/index.html");
    let committed = Metrics::parse(&fs::read_to_string(&metrics_path).unwrap_or_default());
    let bless = blessing();
    let full = std::env::var_os("FORMAL_COMPARISONS_FULL").is_some();
    let strict = std::env::var_os("FORMAL_COMPARISONS_STRICT").is_some();

    let tooling = discover_tooling();
    eprintln!("comparisons: tooling {tooling:#?}");

    // formal itself is always required: qemu + the RISC-V binutils are the same
    // hard requirement every QEMU-booting test has.
    assert!(
        tooling.get("qemu").is_some() && tooling.get("binutils").is_some(),
        "comparisons: user-mode qemu-riscv64 and the RISC-V binutils (as/ld/objdump/strip) \
         are REQUIRED (install them / set RISCV_BIN)"
    );
    let plugin = ensure_plugin(true).expect(
        "comparisons: the formal_stats TCG plugin could not be provisioned; a \
         plugin-enabled user-mode qemu-riscv64 is required (Ubuntu's qemu-user is \
         built without plugin support - build QEMU with --enable-plugins, see \
         .github/workflows/comparisons.yml)",
    );

    // Which languages can be measured in this run: the toolchain must exist,
    // and in check mode it must match the recorded environment (measuring under
    // a different compiler version would produce legitimate differences that
    // are not regressions).
    let mut skipped: Vec<String> = Vec::new();
    let available = |language: &str, tooling: &Tooling| -> bool {
        required_tools(language)
            .iter()
            .all(|key| tooling.get(key).is_some())
    };
    let matches_recorded = |language: &str, tooling: &Tooling, committed: &Metrics| -> bool {
        // A fresh file (or a tool never recorded before) has nothing to match.
        required_tools(language)
            .iter()
            .all(|key| match committed.environment.get(*key) {
                None => true,
                Some(recorded) => tooling.get(key).as_deref() == Some(recorded.as_str()),
            })
    };

    let mut measured = Metrics::default();
    for language in LANGUAGES {
        if !available(language, &tooling) {
            skipped.push(format!("{language}: pinned toolchain not installed"));
            continue;
        }
        if !bless && !matches_recorded(language, &tooling, &committed) {
            skipped.push(format!(
                "{language}: installed toolchain differs from the recorded environment \
                 (re-measure with BLESS=1 to adopt it)"
            ));
            continue;
        }
        for program in PROGRAMS {
            eprintln!("comparisons: measuring {program}/{language}...");
            let m = measure(program, language, &plugin, full, manifest);
            measured.set(
                "formal_comparison_compile_seconds",
                program,
                language,
                Sample {
                    value: m.compile_seconds,
                    origin: Origin::Measured,
                },
            );
            measured.set(
                "formal_comparison_static_instructions",
                program,
                language,
                Sample {
                    value: m.static_instructions as f64,
                    origin: Origin::Measured,
                },
            );
            measured.set(
                "formal_comparison_binary_bytes",
                program,
                language,
                Sample {
                    value: m.binary_bytes as f64,
                    origin: Origin::Measured,
                },
            );
            if let Some(runtime) = m.runtime {
                measured.set(
                    "formal_comparison_executed_instructions",
                    program,
                    language,
                    Sample {
                        value: runtime.executed_instructions as f64,
                        origin: Origin::Measured,
                    },
                );
                measured.set(
                    "formal_comparison_peak_memory_kib",
                    program,
                    language,
                    Sample {
                        value: runtime.peak_memory_kib as f64,
                        origin: Origin::Measured,
                    },
                );
                measured.set(
                    "formal_comparison_run_seconds",
                    program,
                    language,
                    Sample {
                        value: runtime.run_seconds,
                        origin: Origin::Measured,
                    },
                );
            }
            eprintln!(
                "comparisons: {program}/{language}: compile {}, {} instructions, {} bytes{}",
                fmt_time(m.compile_seconds),
                fmt_group(m.static_instructions),
                fmt_group(m.binary_bytes),
                m.runtime
                    .map(|r| format!(
                        ", {} executed, {}, {}",
                        fmt_group(r.executed_instructions),
                        fmt_mem(r.peak_memory_kib),
                        fmt_time(r.run_seconds)
                    ))
                    .unwrap_or_default()
            );
        }
    }
    for s in &skipped {
        eprintln!("comparisons: SKIPPED {s}");
    }
    assert!(
        !strict || skipped.is_empty(),
        "comparisons: languages skipped under FORMAL_COMPARISONS_STRICT:\n  {}",
        skipped.join("\n  ")
    );
    assert!(
        measured.samples.keys().any(|(_, _, l)| l == "formal"),
        "comparisons: formal itself was not measured"
    );

    if bless {
        let mut merged = committed;
        for (key, sample) in &measured.samples {
            merged.samples.insert(key.clone(), *sample);
        }
        merged.environment = tooling.0;
        fs::write(&metrics_path, merged.render()).expect("write metrics.prom");
        let html = fs::read_to_string(&html_path).expect("read index.html");
        let updated = update_html(&html, &merged).expect("update index.html");
        fs::write(&html_path, updated).expect("write index.html");
        eprintln!("comparisons: blessed tests/comparisons/metrics.prom and index.html");
        return;
    }

    // Check mode: every freshly measured deterministic metric must reproduce
    // the committed value; and the page must be in sync with the file.
    let mut failures: Vec<String> = Vec::new();
    for ((metric, program, language), sample) in &measured.samples {
        let Some(committed_sample) = committed.get(metric, program, language) else {
            failures.push(format!(
                "{metric}{{{program},{language}}}: measured {} but the committed file has \
                 no value; re-baseline with BLESS=1",
                sample.value
            ));
            continue;
        };
        let delta = (sample.value - committed_sample.value).abs();
        let relative = if committed_sample.value != 0.0 {
            delta / committed_sample.value.abs()
        } else if delta == 0.0 {
            0.0
        } else {
            f64::INFINITY
        };
        if committed_sample.origin == Origin::Legacy {
            // Imported pre-pipeline values: informational until re-blessed.
            eprintln!(
                "comparisons: legacy {metric}{{{program},{language}}}: committed {} vs \
                 measured {} (bless to adopt the measured value)",
                committed_sample.value, sample.value
            );
            continue;
        }
        match policy(metric, program, language) {
            Policy::Informational => {
                if relative > 0.5 {
                    eprintln!(
                        "comparisons: note: {metric}{{{program},{language}}} drifted \
                         {committed} -> {measured} (timings are machine-dependent and \
                         not compared; BLESS=1 refreshes them)",
                        committed = committed_sample.value,
                        measured = sample.value,
                    );
                }
            }
            Policy::Tolerance(tolerance) => {
                if relative > tolerance {
                    failures.push(format!(
                        "{metric}{{{program},{language}}}: committed {} vs measured {} \
                         (beyond the {:.0}% tolerance)",
                        committed_sample.value,
                        sample.value,
                        tolerance * 100.0
                    ));
                }
            }
            Policy::Exact => {
                if sample.value != committed_sample.value {
                    failures.push(format!(
                        "{metric}{{{program},{language}}}: committed {} vs measured {}",
                        committed_sample.value, sample.value
                    ));
                }
            }
        }
    }
    let html = fs::read_to_string(&html_path).expect("read index.html");
    match update_html(&html, &committed) {
        Ok(updated) => {
            if updated != html {
                failures.push(
                    "index.html is out of sync with tests/comparisons/metrics.prom \
                     (regenerate with `cargo run --example update_website`, or BLESS=1)"
                        .to_string(),
                );
            }
        }
        Err(e) => failures.push(e),
    }
    assert!(
        failures.is_empty(),
        "comparisons: the measured metrics no longer reproduce \
         tests/comparisons/metrics.prom. If the behaviour change is intended, \
         re-baseline with BLESS=1 (never loosen this to hide a regression):\n  {}",
        failures.join("\n  ")
    );
}

/// The comparison policy for one metric cell (see the module docs): timings are
/// informational, formal's 2-thread fannkuch runtime figures get a tolerance
/// (thread scheduling genuinely varies), everything else is exact.
enum Policy {
    Exact,
    Tolerance(f64),
    Informational,
}

/// The environment-info labels a language's measurement depends on: it is only
/// comparable against the committed file when these all match the recorded
/// values.
fn required_tools(language: &str) -> &'static [&'static str] {
    match language {
        "formal" => &["binutils", "qemu"],
        "rust" => &["rustc", "binutils", "qemu"],
        "c" | "cpp" | "zig" => &["zig", "binutils", "qemu"],
        "ada" => &["gnat"],
        _ => unreachable!(),
    }
}

fn policy(metric: &str, program: &str, language: &str) -> Policy {
    if metric.ends_with("_seconds") {
        return Policy::Informational;
    }
    if (metric == "formal_comparison_executed_instructions"
        || metric == "formal_comparison_peak_memory_kib")
        && program == "fannkuch"
        && language == "formal"
    {
        return Policy::Tolerance(0.10);
    }
    Policy::Exact
}

// ---------------------------------------------------------------------------
// Tooling discovery / the environment-info labels.
// ---------------------------------------------------------------------------

/// The resolved environment: label -> value, exactly what the environment-info
/// metric records (`host`, `os`, `qemu`, `binutils`, `rustc`, `zig`, `gnat`;
/// a missing tool simply has no entry).
#[derive(Debug)]
struct Tooling(std::collections::BTreeMap<String, String>);

impl Tooling {
    fn get(&self, key: &str) -> Option<String> {
        self.0.get(key).cloned()
    }
}

fn discover_tooling() -> Tooling {
    let bin = riscv_bin();
    let zig = zig_command();
    let toolchain = rust_toolchain();
    let script = format!(
        r#"BIN="{bin}"
QEMU="${{BIN:+$BIN/}}qemu-riscv64"
AS="${{BIN:+$BIN/}}riscv64-unknown-elf-as"
RUSTC="$(command -v rustc || echo "$HOME/.cargo/bin/rustc")"
command -v "$QEMU" >/dev/null 2>&1 && echo "qemu=$("$QEMU" --version | head -1 | sed 's/.*version //;s/ .*//')"
command -v "$AS" >/dev/null 2>&1 && echo "binutils=$("$AS" --version | head -1 | awk '{{print $NF}}')"
"$RUSTC" +{toolchain} --version >/dev/null 2>&1 && echo "rustc=$("$RUSTC" +{toolchain} --version | sed 's/^rustc //')"
{zig} version >/dev/null 2>&1 && echo "zig=$({zig} version)"
command -v gnatmake >/dev/null 2>&1 && echo "gnat=$(gnatmake --version | head -1 | awk '{{print $NF}}')"
echo "host=$(grep -m1 'model name' /proc/cpuinfo | sed 's/.*: //') ($(nproc) cores)"
echo "os=$(. /etc/os-release && echo "$PRETTY_NAME"), Linux $(uname -r)"
"#
    );
    let output = toolchain_shell(&script)
        .output()
        .expect("failed to invoke the toolchain shell for tool discovery");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let mut map = std::collections::BTreeMap::new();
    for line in stdout.lines() {
        if let Some((key, value)) = line.split_once('=') {
            if !value.trim().is_empty() {
                map.insert(key.trim().to_string(), value.trim().to_string());
            }
        }
    }
    Tooling(map)
}

/// The `zig` invocation for the scripts: `FORMAL_ZIG` (a path) or `zig` from
/// `PATH`, quoted for bash.
fn zig_command() -> String {
    match std::env::var("FORMAL_ZIG") {
        Ok(path) if !path.is_empty() => format!("\"{path}\""),
        _ => "zig".to_string(),
    }
}

/// The rustup toolchain the Rust builds pin: `FORMAL_RUST_TOOLCHAIN` (CI pins a
/// dated nightly there) or plain `nightly`. Whatever resolves is recorded in
/// the environment info, so a different nightly shows up as an environment
/// mismatch, not as inexplicable numeric drift.
fn rust_toolchain() -> String {
    std::env::var("FORMAL_RUST_TOOLCHAIN").unwrap_or_else(|_| "nightly".to_string())
}

// ---------------------------------------------------------------------------
// Measurement.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy)]
struct Runtime {
    executed_instructions: u64,
    peak_memory_kib: u64,
    run_seconds: f64,
}

struct Measured {
    compile_seconds: f64,
    static_instructions: u64,
    binary_bytes: u64,
    runtime: Option<Runtime>,
}

/// Measures one `program` x `language` cell: build (timed), static metrics,
/// and - where the language runs on RISC-V and the mode allows - the
/// instrumented + timed runs. Panics (failing the test) on any build or run
/// failure: a comparison that cannot be measured faithfully must not silently
/// report anything.
fn measure(program: &str, language: &str, plugin: &str, full: bool, manifest: &str) -> Measured {
    let dir = format!("{manifest}/target/comparisons/{program}-{language}");
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).expect("create the comparison work dir");

    let (compile_seconds, static_instructions) = match language {
        "formal" => build_formal(program, &dir),
        "rust" => build_rust(program, &dir, manifest),
        "c" | "cpp" => build_zig_cc(program, language, &dir, manifest),
        "zig" => build_zig(program, &dir, manifest),
        "ada" => build_ada(program, &dir, manifest),
        _ => unreachable!(),
    };
    let binary_bytes = fs::metadata(format!("{dir}/prog.elf"))
        .expect("stat the built binary")
        .len();

    // Ada is build-only (no RISC-V Ada toolchain); fannkuch's runtime runs are
    // gated behind FORMAL_COMPARISONS_FULL (minutes to hours).
    let runtime = if language == "ada" || (program == "fannkuch" && !full) {
        None
    } else {
        Some(run_riscv(program, language, &dir, plugin))
    };

    Measured {
        compile_seconds,
        static_instructions,
        binary_bytes,
        runtime,
    }
}

/// Runs `script` via the toolchain shell, panicking with full output on
/// failure.
fn shell_ok(context: &str, script: &str) -> String {
    let output = toolchain_shell(script)
        .output()
        .unwrap_or_else(|e| panic!("{context}: failed to invoke the toolchain shell: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "{context} failed:\n--- stdout ---\n{stdout}\n--- stderr ---\n{stderr}"
    );
    stdout
}

/// The compile-seconds echoed by a build script as `===COMPILE===<seconds>`.
fn parse_compile_seconds(context: &str, stdout: &str) -> f64 {
    between(stdout, "===COMPILE===", "\n")
        .trim()
        .parse()
        .unwrap_or_else(|_| panic!("{context}: no ===COMPILE=== marker in:\n{stdout}"))
}

/// Counts the machine instructions in formal's emitted assembly: exactly the
/// site's `grep -cE '^    [a-z]'` (four spaces then a lowercase mnemonic).
fn count_asm_instructions(asm: &str) -> u64 {
    asm.lines()
        .filter(|line| {
            line.strip_prefix("    ")
                .and_then(|rest| rest.chars().next())
                .is_some_and(|c| c.is_ascii_lowercase())
        })
        .count() as u64
}

/// The stripped binary's instruction count via the RISC-V objdump, exactly the
/// site's `objdump -d prog.elf | grep -cE '^[[:space:]]+[0-9a-f]+:'`. `host`
/// selects the host objdump (Ada's x86 build) over the RISC-V one.
fn objdump_count(dir: &str, host: bool) -> u64 {
    let bin = riscv_bin();
    let dir_sh = script_path(dir);
    let host = if host { "true" } else { "false" };
    let script = format!(
        r#"set -e
BIN="{bin}"
if {host}; then OD=objdump; else OD="${{BIN:+$BIN/}}riscv64-unknown-elf-objdump"; fi
cd "{dir_sh}"
"$OD" -d prog.elf | grep -cE '^[[:space:]]+[0-9a-f]+:'
"#
    );
    shell_ok("objdump instruction count", &script)
        .trim()
        .parse()
        .expect("parse the objdump instruction count")
}

/// Strips `prog.elf` in place (all comparisons measure the stripped binary).
fn strip_binary(dir: &str, host: bool) {
    let bin = riscv_bin();
    let dir_sh = script_path(dir);
    let host = if host { "true" } else { "false" };
    let script = format!(
        r#"set -e
BIN="{bin}"
if {host}; then ST=strip; else ST="${{BIN:+$BIN/}}riscv64-unknown-elf-strip"; fi
cd "{dir_sh}"
"$ST" prog.elf
"#
    );
    shell_ok("strip", &script);
}

/// formal: translate + verify + emit in-process, then assemble + link - all of
/// it is the compile. `hello` is the hosted `tests/linux_hello` program
/// (1 hart, `emit_executable`); `fannkuch` is `tests/fannkuch_v2` (2 harts as
/// real OS threads, `emit_executable_hosted`).
fn build_formal(program: &str, dir: &str) -> (f64, u64) {
    let started = Instant::now();
    let (asset, harts) = match program {
        "hello" => ("linux_hello/dialect.s", 1),
        "fannkuch" => ("fannkuch_v2/dialect.s", 2),
        _ => unreachable!(),
    };
    let mut ast = setup_test(asset);
    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts,
            }],
        )
        .expect("failed to construct the verifier")
    };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    } = expect_valid(&trace, result);
    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }
    let asm = if harts == 1 {
        emit_executable(
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    } else {
        emit_executable_hosted(
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    fs::write(format!("{dir}/prog.s"), &asm).expect("write the emitted assembly");

    let bin = riscv_bin();
    let dir_sh = script_path(dir);
    let script = format!(
        r#"set -e
BIN="{bin}"
AS="${{BIN:+$BIN/}}riscv64-unknown-elf-as"
LD="${{BIN:+$BIN/}}riscv64-unknown-elf-ld"
cd "{dir_sh}"
"$AS" -march=rv64gcv -o prog.o prog.s
"$LD" --no-relax -e _start -o prog.elf prog.o
"#
    );
    shell_ok("formal assemble+link", &script);
    let compile_seconds = started.elapsed().as_secs_f64();
    strip_binary(dir, false);
    (compile_seconds, count_asm_instructions(&asm))
}

/// Rust: the site's minimal-std release build (nightly, `-Zbuild-std`,
/// opt-level=z, LTO, panic=immediate-abort, stripped), targeted at
/// riscv64gc-unknown-linux-musl and linked self-contained with rust-lld (no C
/// cross-toolchain involved). Cold target dir; the measured time is the whole
/// build including std.
fn build_rust(program: &str, dir: &str, manifest: &str) -> (f64, u64) {
    let crate_dir = format!("{dir}/crate");
    fs::create_dir_all(format!("{crate_dir}/src")).expect("create the crate dir");
    fs::write(
        format!("{crate_dir}/Cargo.toml"),
        "[package]\nname = \"prog\"\nversion = \"0.0.0\"\nedition = \"2021\"\n\n[workspace]\n",
    )
    .expect("write Cargo.toml");
    let source = fs::read_to_string(format!(
        "{manifest}/tests/comparisons/programs/{program}.rs"
    ))
    .expect("read the Rust source");
    fs::write(format!("{crate_dir}/src/main.rs"), source).expect("write main.rs");

    let dir_sh = script_path(dir);
    let toolchain = rust_toolchain();
    let script = format!(
        r#"set -e
cd "{dir_sh}/crate"
CARGO="$(command -v cargo || echo "$HOME/.cargo/bin/cargo")"
export CARGO_TARGET_DIR="{dir_sh}/cargo-target"
rm -rf "$CARGO_TARGET_DIR"
TS=$(date +%s.%N)
CARGO_PROFILE_RELEASE_OPT_LEVEL=z CARGO_PROFILE_RELEASE_LTO=true \
CARGO_PROFILE_RELEASE_CODEGEN_UNITS=1 CARGO_PROFILE_RELEASE_PANIC=abort \
CARGO_PROFILE_RELEASE_STRIP=true \
RUSTFLAGS='-Zlocation-detail=none -Zfmt-debug=none -Zunstable-options -Cpanic=immediate-abort -Ctarget-feature=+crt-static -Clinker=rust-lld -Clink-self-contained=yes' \
"$CARGO" +{toolchain} build --release --target riscv64gc-unknown-linux-musl \
    -Zbuild-std=std,panic_abort -Zbuild-std-features= >build.log 2>&1
TE=$(date +%s.%N)
echo "===COMPILE===$(awk "BEGIN{{print $TE-$TS}}")"
cp "$CARGO_TARGET_DIR/riscv64gc-unknown-linux-musl/release/prog" ../prog.elf
"#
    );
    let stdout = shell_ok("rust build", &script);
    let compile_seconds = parse_compile_seconds("rust build", &stdout);
    strip_binary(dir, false);
    (compile_seconds, objdump_count(dir, false))
}

/// C / C++: `zig cc` / `zig c++` (clang + musl under the hood - the one pinned
/// toolchain that cross-compiles both to static riscv64-linux-musl), `-Os`,
/// gc-sections. A warm-up build (differing only by a `-D`) populates the
/// shared global cache (musl/compiler-rt/libc++) so the measured build is a
/// plain compile, not a one-time toolchain bootstrap; the local cache is
/// per-build.
fn build_zig_cc(program: &str, language: &str, dir: &str, manifest: &str) -> (f64, u64) {
    let (ext, subcommand) = match language {
        "c" => ("c", "cc"),
        "cpp" => ("cpp", "c++"),
        _ => unreachable!(),
    };
    let source = format!("{manifest}/tests/comparisons/programs/{program}.{ext}");
    fs::copy(&source, format!("{dir}/prog.{ext}")).expect("copy the source");
    let zig = zig_command();
    let dir_sh = script_path(dir);
    let global_cache = script_path(&format!("{manifest}/target/comparisons/zig-global-cache"));
    let script = format!(
        r#"set -e
cd "{dir_sh}"
export ZIG_GLOBAL_CACHE_DIR="{global_cache}"
export ZIG_LOCAL_CACHE_DIR="$PWD/zig-local-cache"
FLAGS="-target riscv64-linux-musl -Os -static -ffunction-sections -fdata-sections -Wl,--gc-sections"
{zig} {subcommand} $FLAGS -DFORMAL_WARMUP=1 -o warmup.elf prog.{ext} >warmup.log 2>&1
rm -rf "$ZIG_LOCAL_CACHE_DIR"
TS=$(date +%s.%N)
{zig} {subcommand} $FLAGS -o prog.elf prog.{ext} >build.log 2>&1
TE=$(date +%s.%N)
echo "===COMPILE===$(awk "BEGIN{{print $TE-$TS}}")"
"#
    );
    let stdout = shell_ok("zig cc build", &script);
    let compile_seconds = parse_compile_seconds("zig cc build", &stdout);
    strip_binary(dir, false);
    (compile_seconds, objdump_count(dir, false))
}

/// Zig: `zig build-exe -O ReleaseSmall` for static riscv64-linux-musl. Same
/// warm-up discipline as [`build_zig_cc`] (the warm-up compiles a copy of the
/// source with an appended comment so it does not cache-hit the measured
/// build).
fn build_zig(program: &str, dir: &str, manifest: &str) -> (f64, u64) {
    let source = fs::read_to_string(format!(
        "{manifest}/tests/comparisons/programs/{program}.zig"
    ))
    .expect("read the Zig source");
    fs::write(format!("{dir}/prog.zig"), &source).expect("write the Zig source");
    fs::write(format!("{dir}/warmup.zig"), format!("{source}// warmup\n"))
        .expect("write the warm-up source");
    let zig = zig_command();
    let dir_sh = script_path(dir);
    let global_cache = script_path(&format!("{manifest}/target/comparisons/zig-global-cache"));
    let script = format!(
        r#"set -e
cd "{dir_sh}"
export ZIG_GLOBAL_CACHE_DIR="{global_cache}"
export ZIG_LOCAL_CACHE_DIR="$PWD/zig-local-cache"
{zig} build-exe -O ReleaseSmall -target riscv64-linux-musl -femit-bin=warmup.elf warmup.zig >warmup.log 2>&1
rm -rf "$ZIG_LOCAL_CACHE_DIR"
TS=$(date +%s.%N)
{zig} build-exe -O ReleaseSmall -target riscv64-linux-musl -femit-bin=prog.elf prog.zig >build.log 2>&1
TE=$(date +%s.%N)
echo "===COMPILE===$(awk "BEGIN{{print $TE-$TS}}")"
"#
    );
    let stdout = shell_ok("zig build", &script);
    let compile_seconds = parse_compile_seconds("zig build", &stdout);
    strip_binary(dir, false);
    (compile_seconds, objdump_count(dir, false))
}

/// Ada: `gnatmake`, static, on the **host** (no RISC-V Ada toolchain is
/// available, so Ada is compared statically only - the site says so). `-O2`
/// for hello and `-Os` + gc-sections for fannkuch, mirroring the page's
/// commands; the binary is stripped and counted with the host objdump.
fn build_ada(program: &str, dir: &str, manifest: &str) -> (f64, u64) {
    let source = format!("{manifest}/tests/comparisons/programs/{program}.adb");
    fs::copy(&source, format!("{dir}/{program}.adb")).expect("copy the Ada source");
    let dir_sh = script_path(dir);
    // `-bargs -static` picks the static GNAT runtime by path; Debian's gnatlink
    // otherwise asks the linker for `-lgnat-13`, which only exists shared.
    let flags = match program {
        "hello" => "-O2 hello.adb -bargs -static -largs -static",
        "fannkuch" => "-Os fannkuch.adb -bargs -static -largs -static -Wl,--gc-sections",
        _ => unreachable!(),
    };
    let script = format!(
        r#"set -e
cd "{dir_sh}"
TS=$(date +%s.%N)
gnatmake {flags} >build.log 2>&1
TE=$(date +%s.%N)
echo "===COMPILE===$(awk "BEGIN{{print $TE-$TS}}")"
mv {program} prog.elf
"#
    );
    let stdout = shell_ok("gnatmake build", &script);
    let compile_seconds = parse_compile_seconds("gnatmake build", &stdout);
    strip_binary(dir, true);
    (compile_seconds, objdump_count(dir, true))
}

/// Runs `prog.elf` under user-mode qemu-riscv64 under controlled conditions -
/// `cd` into the build dir, **empty guest environment** (`env -i`), the fixed
/// relative `./prog.elf` argv - once instrumented with the `formal_stats`
/// plugin (exact instruction count + working set) and then plugin-free for the
/// wall-clock time (best of 3 for the sub-second hello). Asserts the program
/// produced its expected output on every run.
fn run_riscv(program: &str, language: &str, dir: &str, plugin: &str) -> Runtime {
    let bin = riscv_bin();
    let dir_sh = script_path(dir);
    // The instrumented run gets a far longer allowance than the timed one: the
    // plugin's per-access working-set callback slows a heavy compute several-fold.
    let (instrumented_timeout, timed_timeout, timed_runs) = match program {
        "hello" => (120, 120, 3),
        _ => (28800, 3600, 1),
    };
    let script = format!(
        r#"set -e
BIN="{bin}"
QEMU="$(command -v "${{BIN:+$BIN/}}qemu-riscv64")"
cd "{dir_sh}"
rm -f plugin.stats
timeout {instrumented_timeout} env -i "$QEMU" -plugin "{plugin},out=$PWD/plugin.stats" ./prog.elf >run.out 2>run.err || echo "===CRASH===$?"
for i in $(seq 1 {timed_runs}); do
  TS=$(date +%s.%N)
  timeout {timed_timeout} env -i "$QEMU" ./prog.elf >timed.out 2>timed.err || echo "===CRASH===$?"
  TE=$(date +%s.%N)
  echo "===TIME===$(awk "BEGIN{{print $TE-$TS}}")"
done
"#
    );
    let stdout = shell_ok(&format!("{program}/{language} qemu run"), &script);
    assert!(
        !stdout.contains("===CRASH==="),
        "{program}/{language}: the program did not exit cleanly under qemu-riscv64:\n{stdout}\n{}\n{}",
        fs::read_to_string(format!("{dir}/run.err")).unwrap_or_default(),
        fs::read_to_string(format!("{dir}/timed.err")).unwrap_or_default(),
    );
    // Best (minimum) of the timed runs: the least-disturbed measurement.
    let run_seconds = stdout
        .lines()
        .filter_map(|line| line.strip_prefix("===TIME==="))
        .filter_map(|t| t.trim().parse::<f64>().ok())
        .fold(f64::INFINITY, f64::min);
    assert!(
        run_seconds.is_finite(),
        "{program}/{language}: no ===TIME=== in:\n{stdout}"
    );

    // The expected output; Zig's hello prints via std.debug.print (stderr), so
    // check stdout + stderr combined.
    let output = format!(
        "{}{}",
        fs::read_to_string(format!("{dir}/run.out")).unwrap_or_default(),
        fs::read_to_string(format!("{dir}/run.err")).unwrap_or_default()
    );
    match program {
        "hello" => assert!(
            output.contains("Hello World!"),
            "{program}/{language}: expected \"Hello World!\", got:\n{output}"
        ),
        "fannkuch" => assert!(
            output.contains("3968050") && output.contains("Pfannkuchen(12) = 65"),
            "{program}/{language}: expected the fannkuch(12) reference output, got:\n{output}"
        ),
        _ => unreachable!(),
    }

    let stats = parse_plugin_stats(
        &fs::read_to_string(format!("{dir}/plugin.stats"))
            .unwrap_or_else(|_| panic!("{program}/{language}: the plugin wrote no stats")),
    );
    Runtime {
        executed_instructions: stats
            .instructions
            .unwrap_or_else(|| panic!("{program}/{language}: no instruction count in the stats")),
        peak_memory_kib: stats
            .peak_kib()
            .unwrap_or_else(|| panic!("{program}/{language}: no peak memory in the stats")),
        run_seconds,
    }
}
