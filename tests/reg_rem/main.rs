#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Register-register remainder coverage: two `rem` (17 % 5, 100 % 7) plus an
/// `add`, with the total proven at compile time by the `require`. Exercises the
/// `rem` instruction end to end -- the hl lowering (`reg = a % b`), the verifier's
/// symbolic remainder (the narrowing primitive `assume:` uses), and codegen --
/// and is only `Valid` if the verifier computes the remainders correctly. The
/// program then computes and exits 0 with no output.
#[test]
fn reg_rem() {
    let mut ast = setup_test("reg_rem/dialect.s");
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
    bless_asm("reg_rem/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("reg_rem", &asm);
    assert_eq!(
        stdout, "",
        "reg_rem computes and exits cleanly with no output"
    );
}
