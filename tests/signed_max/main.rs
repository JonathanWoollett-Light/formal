#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Maximum of an array of signed 32-bit values, proven at compile time:
/// `max([-5 3 -1 -8 2]) == 3`. The running `if nums[i] > max` compares signed
/// `i32` values loaded from memory, exercising the signed-comparison path the
/// unsigned sort/search programs never reach; boots under `qemu-riscv64`.
#[test]
fn signed_max() {
    let mut ast = setup_test("signed_max/dialect.s");
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
        "signed_max/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("signed_max", &asm);
    assert_eq!(
        stdout, "",
        "signed_max computes and exits cleanly with no output"
    );
}
