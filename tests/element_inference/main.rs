#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;
use verifier_types::*;

/// **Element indexing an inferred variable.** `t0[0]` states no width, so the
/// access is as wide as the type inference settles on, and inference settles on
/// the narrowest type under which the program is *provable*: storing 300 and
/// proving it reads back rejects `u8`/`i8` (they truncate it to 44, so the
/// `require` fails) and lands on `u16`. The emitted program is a 2-byte
/// `sh`/`lhu` over 2 bytes of `.bss`, and it boots under `qemu-riscv64`.
///
/// The contrast with `inferred_widening` is the point: there a *byte slice*
/// (`t3[0:4]`) tells the verifier the width up front and pins `u32`; here the
/// program never states a width and the proof obligation picks it.
#[test]
fn element_inference() {
    let mut ast = setup_test("element_inference/dialect.s");
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

    // The narrowest type that proves the program, not the widest that fits.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U16))]
                .into_iter()
                .collect()
        ),
        "storing 300 through `value[0]` should infer `value: global u16`"
    );

    // `accessed` unions every configuration explored, so the rejected `u8`
    // candidate's single byte is still recorded beside the `u16` pair: an
    // over-approximation, which is what dead-data elimination needs. The
    // *lowering* cannot work that way (one directive becomes one instruction),
    // which is why backtracking drops the lowerings of the variable it
    // re-types -- the emitted `sh`/`lhu` below is the proof it did.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 1), (0, 2)].into_iter().collect())]
            .into_iter()
            .collect::<AccessedRanges>(),
        "the accessed union covers the rejected u8 candidate and the u16 it settled on"
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
        &indexed,
    );
    // The element load extends the way the verifier modelled it: `u16` is
    // unsigned, so `lhu`, not `lh`.
    assert!(
        asm.contains("sh t1, 0(t0)") && asm.contains("lhu t2, 0(t0)"),
        "the resolved element access should be a 2-byte unsigned pair:\n{asm}"
    );
    bless_asm(
        "element_inference/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("element_inference", &asm);
    assert_eq!(
        stdout, "",
        "element_inference computes and exits cleanly with no output"
    );
}
