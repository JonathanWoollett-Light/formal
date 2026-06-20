#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Runtime input the verifier cannot see.** A literal `12` is written into a
/// declared `#@` region and read back through a raw address; a raw-region load
/// yields the *full range*, so the verifier treats `n` as unknown (it cannot
/// constant-fold), while at runtime the region holds `12`. The program then
/// narrows `n % 4` to `0..3` and indexes a 4-element array -- provably in-bounds
/// for *any* `n`, which is the whole point: safety is proven without the value.
///
/// This is the mechanism the fannkuch(n=12) programs use to keep the verifier
/// from unrolling the search around a known `n`. It boots bare-metal under QEMU
/// (it touches raw RAM) and exits cleanly with no output.
#[test]
fn runtime_input() {
    let mut ast = setup_test("runtime_input/dialect.s");
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
        "runtime_input/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // Bare-metal boot: writes 12 into the region, reads it back, indexes safely.
    let serial = unsafe {
        run_program(
            "runtime_input",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "runtime_input exits cleanly with no output");
}
