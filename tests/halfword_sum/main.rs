#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// 16-bit (`u16`) values via 2-byte halfword load/store (`sh`/`lh`): stores
/// 1000, 2000, 3000 into a `[u16]` array, reads them back and proves the sum is
/// 6000. The first program to exercise the 2-byte access width and the `u16`
/// value-model paths; boots under `qemu-riscv64` and exits 0.
#[test]
fn halfword_sum() {
    let mut ast = setup_test("halfword_sum/dialect.s");
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
        "halfword_sum/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("halfword_sum", &asm);
    assert_eq!(
        stdout, "",
        "halfword_sum computes and exits cleanly with no output"
    );
}
