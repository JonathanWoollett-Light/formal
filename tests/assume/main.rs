#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// The **`forget` + `assume:` idiom**. `a0` holds 12 at runtime; `forget a0`
/// havocs it (so the verifier cannot optimise around the value), and the
/// `assume:` block narrows it to the concrete `5` for verification only. Both are
/// dropped from the binary. With `a0 = 5` the `while i != a0` loop is determinate,
/// so the verifier proves the `arr[i] = i` fill is memory-safe (for n = 5, a
/// subset of the 16-element array); at runtime `a0 = 12` and the fill covers
/// `arr[0..12]`, still in bounds.
///
/// This is the lynchpin that makes an otherwise-unbounded runtime-`n` search
/// tractable. (Narrowing to a *range* of `n` instead of one value needs
/// indeterminate-branch forking, a separate verifier capability.) The directives
/// are verifier-only -- neither `#~ a0` nor `li a0, 5` appears in the binary -- so
/// it lowers to a hosted ELF and exits cleanly under `qemu-riscv64`.
#[test]
fn assume() {
    let mut ast = setup_test("assume/dialect.s");
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
    // The `forget` and `assume` directives are verified but never emitted.
    assert!(
        !asm.contains("#~") && !asm.contains("li a0, 5"),
        "the forget/assume directives must not appear in the binary:\n{asm}"
    );
    bless_asm("assume/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("assume", &asm);
    assert_eq!(stdout, "", "assume exits cleanly with no output");
}
