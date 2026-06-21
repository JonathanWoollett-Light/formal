#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Difference array proven at compile time: for `arr = [10 7 12 4]` the
/// adjacent differences are `[-3 5 -8]`, and by telescoping their sum equals
/// `arr[3] - arr[0] = -6` (asserted). A standard technique (range updates,
/// discrete derivatives) that subtracts two freshly-loaded signed `i32` values
/// each step -- the signed-subtract path -- then boots under `qemu-riscv64`.
#[test]
fn difference_array() {
    let mut ast = setup_test("difference_array/dialect.s");
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
    bless_asm(
        "difference_array/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("difference_array", &asm);
    assert_eq!(
        stdout, "",
        "difference_array computes and exits cleanly with no output"
    );
}
