#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// The Collatz step count proven at compile time: the verifier follows the
/// hailstone sequence from 7 over concrete values, so `require a1 == 16` is only
/// reachable-as-satisfied if the sequence really reaches 1 in 16 steps. A small
/// real program that combines register-register `div`/`mul`/`rem` with the
/// `if n % 2 == 0` zero-test branches, then boots under `qemu-riscv64` and exits
/// 0 with no output.
#[test]
fn collatz() {
    let mut ast = setup_test("collatz/dialect.s");
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
    bless_asm("collatz/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("collatz", &asm);
    assert_eq!(
        stdout, "",
        "collatz computes and exits cleanly with no output"
    );
}
