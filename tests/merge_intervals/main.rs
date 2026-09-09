#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Merge Intervals proven correct at compile time: `[[2 6] [1 3] [15 18]
/// [8 10]]` is sorted by start and swept into `[[1 6] [8 10] [15 18]]`, with
/// the count and all three pairs asserted by `require`. Exercises two parallel
/// arrays swapped in lockstep and a print loop that survives `print`'s register
/// clobbers. Runs under `qemu-riscv64` and writes the merged intervals.
#[test]
fn merge_intervals() {
    let mut ast = setup_test("merge_intervals/dialect.s");
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
        indexed,
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
        &indexed,
    );
    bless_asm(
        "merge_intervals/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("merge_intervals", &asm);
    assert_eq!(
        stdout, "1 6\n8 10\n15 18",
        "merge_intervals prints the merged intervals"
    );
}
