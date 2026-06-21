#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Signed 32-bit (`i32`) arithmetic with negative values: stores `-100`, `50`,
/// `-25` into an `[i32]` array, reads them back and proves their sum is `-75`.
/// The signed-word counterpart of `signed_bytes`, exercising the value model's
/// `i32` load/store/add paths, then boots under `qemu-riscv64` and exits 0.
#[test]
fn signed_words() {
    let mut ast = setup_test("signed_words/dialect.s");
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
        "signed_words/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("signed_words", &asm);
    assert_eq!(
        stdout, "",
        "signed_words computes and exits cleanly with no output"
    );
}
