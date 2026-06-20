#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Register-register addition coverage: chained `add`s (including a register
/// added to itself) plus an immediate `addi`, with the total proven at compile
/// time by the `require`. This exercises the `add` instruction end to end -- the
/// hl lowering (`reg = a + b` with `b` a register), the verifier's symbolic
/// `add` semantics, and codegen -- and is only `Valid` if the verifier computes
/// the sums correctly. The program then computes and exits 0 with no output.
#[test]
fn reg_add() {
    let mut ast = setup_test("reg_add/dialect.s");
    // The Python-like source translates exactly to the stored dialect.
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
    bless_asm("reg_add/emitted.s", asm.clone(), include_str!("emitted.s"));

    // The total is proven at compile time, so the program just computes and exits
    // 0 with no output.
    let stdout = run_linux("reg_add", &asm);
    assert_eq!(
        stdout, "",
        "reg_add computes and exits cleanly with no output"
    );
}
