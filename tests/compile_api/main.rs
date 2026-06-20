//! Covers the high-level public entry point [`formal::compile`] (and through it
//! `lib.rs`: the `Compiled` result, `print_ast`, and the verify -> optimize ->
//! lower wiring). The other integration tests drive the lower-level `Explorerer`
//! directly; this exercises the one-call pipeline an end user actually uses.

use formal::*;

/// A provable program compiles: the whole pipeline (translate + std prelude,
/// parse, compress, verify, optimize, lower) yields the combined source, the
/// RISC-V dialect, and runnable assembly.
#[test]
fn compile_lowers_a_provable_program() {
    let source = "\
value: global u32
t0 = &value
t1 = 7
t0[0:4] = t1
t2 = t0[0:4]
a0 = 7
require t2 == a0
exit(0)
";
    let compiled = compile(source).expect("a provable program should compile");
    assert!(
        compiled.combined.contains("require"),
        "combined source keeps the program"
    );
    assert!(
        compiled.dialect.contains("sw t1, 0(t0)"),
        "dialect lowers the store: {}",
        compiled.dialect
    );
    assert!(
        compiled.assembly.contains("_start"),
        "assembly has an entry point"
    );
}

/// An unprovable program (an unsatisfiable `require`, so the `#!` fail marker is
/// reachable) is rejected as a `CompileError` rather than producing a binary.
#[test]
fn compile_rejects_an_unprovable_program() {
    let source = "\
value: global u32
t0 = &value
t1 = 7
t0[0:4] = t1
t2 = t0[0:4]
a0 = 8
require t2 == a0
exit(0)
";
    let error = compile(source)
        .map(|_| ())
        .expect_err("an unsatisfiable require must not compile");
    // The error renders (its Display path), so a CLI can report it.
    assert!(!format!("{error}").is_empty());
}

/// A source that fails to even translate (a bad instruction) is reported as a
/// translation error, not a panic.
#[test]
fn compile_reports_a_translation_error() {
    let error = compile("t0 = &\nexit(0)\n")
        .map(|_| ())
        .expect_err("a bad `&` form must fail");
    assert!(!format!("{error}").is_empty());
}
