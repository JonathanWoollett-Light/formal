#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;
use verifier_types::*;

/// Type inference that backtracks through a variable's **mid-program** first
/// encounter. `acc` is declared after some preceding computation, so when the
/// best-to-worst type search rejects every type too narrow for the 4-byte store
/// (u8..i16), each rejection re-attaches the frontier after the encounter's
/// predecessor -- the `invalid_path` arm the tests that declare their inferred
/// variable as the first statement never exercise. The search lands on `u32`,
/// the round-tripped value (42) is proven, and it boots under `qemu-riscv64`.
#[test]
fn inferred_widening() {
    let mut ast = setup_test("inferred_widening/dialect.s");
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

    // The search must have widened all the way to u32 (the 4-byte store).
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("acc"), (LabelLocality::Global, Type::U32))]
                .into_iter()
                .collect()
        ),
        "the 4-byte store should infer `acc: global u32`"
    );

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
        "inferred_widening/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("inferred_widening", &asm);
    assert_eq!(
        stdout, "",
        "inferred_widening computes and exits cleanly with no output"
    );
}
