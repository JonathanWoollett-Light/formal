#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// A zero-terminated u32 array summed and counted with a data-driven loop
/// (`while *p != 0`), the sentinel-terminated iteration pattern none of the
/// counted-loop programs use. The closing `require`s prove the sum (23) and
/// count (6) at compile time, so the loop's termination on the 0 sentinel is
/// part of the proof. Exercises the `beqz`-on-u32 loop-exit resolution over a
/// value loaded from memory, then boots under `qemu-riscv64` and exits 0.
#[test]
fn sentinel_sum() {
    let mut ast = setup_test("sentinel_sum/dialect.s");
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
        "sentinel_sum/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("sentinel_sum", &asm);
    assert_eq!(
        stdout, "",
        "sentinel_sum computes and exits cleanly with no output"
    );
}
