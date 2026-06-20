#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Register-register division coverage: two `div` (100 / 7 = 14, then / 3 = 4),
/// with the result proven at compile time by the `require`. Exercises the `div`
/// instruction end to end -- the hl lowering (`reg = a / b`), the verifier's
/// symbolic integer division, and codegen -- and is only `Valid` if the verifier
/// computes the quotients correctly. The program then computes and exits 0 with
/// no output. (Division drives both the fannkuch index->permutation step and
/// digit extraction for integer printing.)
#[test]
fn reg_div() {
    let mut ast = setup_test("reg_div/dialect.s");
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
    bless_asm("reg_div/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("reg_div", &asm);
    assert_eq!(
        stdout, "",
        "reg_div computes and exits cleanly with no output"
    );
}
