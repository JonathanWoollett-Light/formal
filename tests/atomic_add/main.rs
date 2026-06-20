#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Atomic fetch-add** (`amoadd.w`) end to end: an inline-asm atomic parsed
/// back from the `asm:` block and modeled by the verifier (read-modify-write in
/// one step). The two `require`s prove the returned old value and the
/// incremented counter; booted under `qemu-riscv64`, exiting 0 with no output.
#[test]
fn atomic_add() {
    let mut ast = setup_test("atomic_add/dialect.s");
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
        "atomic_add/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("atomic_add", &asm);
    assert_eq!(
        stdout, "",
        "atomic_add computes and exits cleanly with no output"
    );
}
