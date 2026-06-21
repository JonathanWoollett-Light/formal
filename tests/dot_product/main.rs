#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Dot product of two signed `i32` vectors proven at compile time:
/// `[-1 2 -3] . [4 -5 6] == -32`. Loads signed `i32` pairs from memory,
/// multiplies and accumulates -- exercising signed `i32` multiply, the path the
/// additive/comparison signed tests do not reach -- then boots under
/// `qemu-riscv64` and exits 0.
#[test]
fn dot_product() {
    let mut ast = setup_test("dot_product/dialect.s");
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
        "dot_product/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("dot_product", &asm);
    assert_eq!(
        stdout, "",
        "dot_product computes and exits cleanly with no output"
    );
}
