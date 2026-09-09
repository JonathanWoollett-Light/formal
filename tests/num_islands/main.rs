#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Number of Islands proven correct at compile time: a 4x5 grid holding three
/// islands is flood-filled with an explicit stack (there is no recursion) and
/// the count asserted by `require a3 == 3`. Exercises a program-local `def`
/// inlined at four call sites, and a worklist whose depth drives the loop.
/// Runs under `qemu-riscv64` and writes `3`.
#[test]
fn num_islands() {
    let mut ast = setup_test("num_islands/dialect.s");
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
        "num_islands/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("num_islands", &asm);
    assert_eq!(stdout, "3", "num_islands prints the island count");
}
