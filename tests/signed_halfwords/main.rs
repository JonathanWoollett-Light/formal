#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Signed 16-bit (`i16`) arithmetic with negative values via 2-byte halfword
/// load/store: stores `-1000`, `500`, `-200` into an `[i16]` array, reads them
/// back and proves the sum is `-700`. The signed counterpart of `halfword_sum`,
/// exercising the `i16` value-model paths; boots under `qemu-riscv64` and exits 0.
#[test]
fn signed_halfwords() {
    let mut ast = setup_test("signed_halfwords/dialect.s");
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
        "signed_halfwords/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("signed_halfwords", &asm);
    assert_eq!(
        stdout, "",
        "signed_halfwords computes and exits cleanly with no output"
    );
}
