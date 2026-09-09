#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Two Sum proven correct at compile time: over `nums = [2 7 11 15]` with
/// target 9, the O(n) hash map finds the pair (0, 1), asserted by the two
/// `require`s on the indices. Exercises an open-addressing table indexed by a
/// value loaded out of memory, the canonical non-negative remainder over a
/// complement that goes negative, and `print`'s zero digit (index 0 is
/// printed). Runs under `qemu-riscv64` and writes `0 1`.
#[test]
fn two_sum() {
    let mut ast = setup_test("two_sum/dialect.s");
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
        indexed,
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
        &indexed,
    );
    bless_asm("two_sum/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("two_sum", &asm);
    assert_eq!(stdout, "0 1", "two_sum prints the found index pair");
}
