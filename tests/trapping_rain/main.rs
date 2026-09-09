#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Trapping Rain Water proven correct at compile time: over the bar chart
/// `[0 1 0 2 1 0 1 3 2 1 2 1]` the two-pointer walk accumulates 6 units of
/// water, asserted by `require a6 == 6`. Exercises the complementary-`if` idiom
/// that stands in for `else`, and a running maximum on each side. Runs under
/// `qemu-riscv64` and writes `6`.
#[test]
fn trapping_rain() {
    let mut ast = setup_test("trapping_rain/dialect.s");
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
    bless_asm(
        "trapping_rain/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("trapping_rain", &asm);
    assert_eq!(stdout, "6", "trapping_rain prints the water total");
}
