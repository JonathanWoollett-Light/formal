#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Coin Change proven correct at compile time: the unbounded-knapsack table
/// over coins `[1 2 5]` reaches amount 11 in 3 coins, asserted by
/// `require a3 == 3`. Exercises a dynamic-programming table indexed by a
/// running value, with a sentinel standing in for "unreachable". Runs under
/// `qemu-riscv64` and writes `3`.
#[test]
fn coin_change() {
    let mut ast = setup_test("coin_change/dialect.s");
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
        "coin_change/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("coin_change", &asm);
    assert_eq!(stdout, "3", "coin_change prints the fewest coins");
}
