#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Bubble sort with the sortedness of the result proven at compile time: after
/// the sort, the program `require`s `arr[k] <= arr[k+1]` for every adjacent
/// pair, so the `Valid` outcome IS a proof the array came out sorted. The
/// program exercises computed indexing (`&arr + k*4`, i.e. register-register
/// `mul`/`add`), u32 loads/stores at offsets 0 and 4, and `bge` comparisons
/// over values loaded from memory, then boots under `qemu-riscv64` and exits 0.
#[test]
fn bubble_sort() {
    let mut ast = setup_test("bubble_sort/dialect.s");
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
        "bubble_sort/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("bubble_sort", &asm);
    assert_eq!(
        stdout, "",
        "the sort computes and exits cleanly with no output"
    );
}
