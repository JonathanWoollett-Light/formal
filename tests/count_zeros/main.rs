#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Counts the zero elements of a u32 array (`[3 0 5 0 0 2]` -> 3), proven at
/// compile time. Each `if arr[i] == 0` branches on a value loaded from memory,
/// exercising the `bnez`-on-u32 resolution (fall through on a zero element, jump
/// past the increment on a nonzero one) that the `while != 0` sentinel loop does
/// not reach. Boots under `qemu-riscv64` and exits 0.
#[test]
fn count_zeros() {
    let mut ast = setup_test("count_zeros/dialect.s");
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
        "count_zeros/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("count_zeros", &asm);
    assert_eq!(
        stdout, "",
        "count_zeros computes and exits cleanly with no output"
    );
}
