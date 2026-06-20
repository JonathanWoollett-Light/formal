#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Zero-initialized globals.** A global lives in `.bss` (zero at boot), so the
/// verifier models its initial value as 0. The program reads an *unwritten*
/// global and proves it is 0 with a `require`; booted under `qemu-riscv64` where
/// `.bss` is genuinely zero, so the proof holds at runtime too. Exits 0, no output.
#[test]
fn global_zero_init() {
    let mut ast = setup_test("global_zero_init/dialect.s");
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
        "global_zero_init/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("global_zero_init", &asm);
    assert_eq!(
        stdout, "",
        "global_zero_init computes and exits cleanly with no output"
    );
}
