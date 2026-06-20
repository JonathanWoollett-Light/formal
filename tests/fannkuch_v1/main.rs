#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **fannkuch-redux V1**: single-threaded, pure Python dialect, with the input
/// `n` supplied at runtime. `forget a2` makes the verifier blind to `n` (so it
/// cannot specialise the proof to the value), and an `assume` narrows it to 5 so
/// verification is bounded -- the verifier explores all 5! permutations of
/// fannkuch(5) concretely, proving the array accesses in bounds. The arrays are
/// sized for the maximum n, so a larger runtime n still fits. The computed
/// checksum and max flip count are printed with the polymorphic `print` (integer
/// arm) in the Benchmarks Game format. Booted under `qemu-riscv64`; with the
/// runtime `n` also 5 the output is the known fannkuch(5) answer.
#[test]
fn fannkuch_v1() {
    let mut ast = setup_test("fannkuch_v1/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts: 1,
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

    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    // forget/assume are verifier-only; nothing leaks into the binary.
    assert!(
        !asm.contains("#~") && !asm.contains("#(") && !asm.contains("typeof"),
        "forget/assume/typeof must be resolved at compile time:\n{asm}"
    );
    bless_asm(
        "fannkuch_v1/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // `run_linux` trims surrounding newlines, so the program's trailing "\n" is
    // not seen here; the inner newline (after the checksum) is.
    let stdout = run_linux("fannkuch_v1", &asm);
    assert_eq!(
        stdout, "11\nPfannkuchen(5) = 7",
        "fannkuch(5): checksum 11, max flips 7"
    );
}
