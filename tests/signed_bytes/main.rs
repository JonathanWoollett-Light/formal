#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Signed-byte (`i8`) arithmetic with negative values: stores `-5`, `3`, `-1`
/// into an `[i8]` array, reads them back and proves their sum is `-3`. Exercises
/// the value model's signed-byte load/store/add and the signed compare against a
/// negative immediate -- the `i8` paths the unsigned-only programs do not reach
/// -- then boots under `qemu-riscv64` and exits 0.
#[test]
fn signed_bytes() {
    let mut ast = setup_test("signed_bytes/dialect.s");
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
        "signed_bytes/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("signed_bytes", &asm);
    assert_eq!(
        stdout, "",
        "signed_bytes computes and exits cleanly with no output"
    );
}
