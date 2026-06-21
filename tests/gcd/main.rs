#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Euclid's GCD proven at compile time: `gcd(48, 36) = 12`. The verifier follows
/// the `while b != 0` remainder loop over concrete values, so `require a0 == 12`
/// is the proof. A small real algorithm exercising `rem` whose result feeds back
/// as the next divisor; boots under `qemu-riscv64` and exits 0.
#[test]
fn gcd() {
    let mut ast = setup_test("gcd/dialect.s");
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
    bless_asm("gcd/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("gcd", &asm);
    assert_eq!(stdout, "", "gcd computes and exits cleanly with no output");
}
