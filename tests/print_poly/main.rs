#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Polymorphic `print`, dispatched at compile time.** One `print` handles both
/// a string and an integer: `print("Hi ")` lowers to the byte walk and
/// `print(42)` to the digit formatter, selected by the front-end's `if typeof`
/// dispatch (no runtime type check, no separate `print_int`, and the unmatched
/// arm -- including its otherwise-ill-typed `&msg` on an integer -- is never
/// translated). The two integer prints also exercise call hygiene: each gets a
/// fresh scratch-buffer label, so they do not collide. Booted under
/// `qemu-riscv64`; stdout must be exactly `Hi 427`.
#[test]
fn print_poly() {
    let mut ast = setup_test("print_poly/dialect.s");
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
    // The `typeof` dispatch is compile-time only: no directive leaks into the binary.
    assert!(
        !asm.contains("typeof") && !asm.contains("#~"),
        "the typeof dispatch must be resolved at compile time:\n{asm}"
    );
    bless_asm(
        "print_poly/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("print_poly", &asm);
    assert_eq!(
        stdout, "Hi 427",
        "polymorphic print writes the string then both integers"
    );
}
