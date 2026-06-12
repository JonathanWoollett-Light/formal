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
