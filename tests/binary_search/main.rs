#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Binary search proven correct at compile time: searching the sorted array
/// `[1 3 5 7 9 11]` for `7` lands on index 3, asserted by `require found == 3`.
/// The verifier follows the concrete lo/hi/mid search, exercising computed
/// indexing (`&arr + mid*4`), the `(lo+hi)/2` divide, and the three-way
/// comparison of a loaded `u32` against the target; boots under `qemu-riscv64`.
#[test]
fn binary_search() {
    let mut ast = setup_test("binary_search/dialect.s");
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
        "binary_search/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("binary_search", &asm);
    assert_eq!(
        stdout, "",
        "binary_search computes and exits cleanly with no output"
    );
}
