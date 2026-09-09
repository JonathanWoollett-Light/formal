#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// `print(0)` writes a single `0`. The integer arm of `print` peels decimal
/// digits with `/` and `%`, a loop a zero argument never enters, so before the
/// explicit zero digit in [std/std.hl] the call wrote an empty slice. Printing
/// 0, then 42, then 0 pins the new arm and the ordinary path either side of it,
/// and `dialect.s` pins the inlined expansion so a change to `print` shows up
/// here first. Runs under `qemu-riscv64`.
#[test]
fn print_zero() {
    let mut ast = setup_test("print_zero/dialect.s");
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
        "print_zero/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("print_zero", &asm);
    assert_eq!(stdout, "0 42 0", "print(0) writes a single zero digit");
}
