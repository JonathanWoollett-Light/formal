#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Indexed array access with **computed** indices -- the reason multiply and
/// register-register addition were added. `arr[i]` is `base + i*4` (u32
/// elements), so there is no pointer-walk loop. The program writes `arr[1]` and
/// `arr[3]` at computed addresses, reads them back, sums them (a load + load +
/// `add`), and proves the total at compile time. It exercises pointer + register
/// offset addressing and the `U32`-widening arithmetic on loaded values, then
/// exits 0 with no output.
#[test]
fn indexed() {
    let mut ast = setup_test("indexed/dialect.s");
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
    bless_asm("indexed/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("indexed", &asm);
    assert_eq!(
        stdout, "",
        "indexed computes and exits cleanly with no output"
    );
}
