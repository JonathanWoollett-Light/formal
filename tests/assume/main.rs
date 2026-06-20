#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// The **`assume:` directive**: the verifier executes the block to narrow its
/// symbolic state, but codegen drops it from the binary, so the runtime keeps the
/// original value. Here a runtime-unknown `n` (12 at runtime, read through a
/// region so the verifier cannot see it) is narrowed to the concrete `5` for
/// verification only -- which makes the `while i != n` loop determinate and lets
/// the verifier prove the `arr[i] = i` fill is memory-safe (for n = 5, a subset
/// of the array). The emitted program contains no `li a0, 5`; at runtime it fills
/// `arr[0..12]`, which is in bounds for the 16-element array.
///
/// This is the lynchpin that makes an otherwise-unbounded runtime-`n` search
/// tractable. (Narrowing to a *range* of `n` instead of one value needs
/// indeterminate-branch forking, a separate verifier capability.) Boots
/// bare-metal under QEMU and exits cleanly.
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
    // The assume block is verified but never emitted.
    assert!(
        !asm.contains("li a0, 5"),
        "the assume block must not appear in the binary:\n{asm}"
    );
    bless_asm("assume/emitted.s", asm.clone(), include_str!("emitted.s"));

    let serial = unsafe {
        run_program(
            "assume",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "assume exits cleanly with no output");
}
