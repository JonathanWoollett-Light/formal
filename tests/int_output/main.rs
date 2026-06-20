#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Integer output** by digit extraction. The program prints the integer `42`
/// to stdout: it divides/remainders by ten to peel digits off the back of a
/// buffer (`div`/`rem`), converts each to ASCII (`+ 48`), tracks the digit count,
/// and writes the slice with the Linux `write(2)` syscall. This is the routine
/// the fannkuch programs use to print their result (the checksum and flip count),
/// and the scalar arm a polymorphic `print` dispatches to. Booted under
/// `qemu-riscv64`; the captured stdout must be exactly `42`.
#[test]
fn int_output() {
    let mut ast = setup_test("int_output/dialect.s");
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
        "int_output/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("int_output", &asm);
    assert_eq!(stdout, "42", "int_output prints the integer 42");
}
