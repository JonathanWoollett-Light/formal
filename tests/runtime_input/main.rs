#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **A value the verifier cannot see, via `forget`.** `a0` holds `12` at runtime,
/// but `forget a0` havocs it to *any* value for the verifier. The verifier then
/// proves `arr[a0 % 4]` is in bounds for *every* `a0` -- safety proven without the
/// value -- while the runtime keeps `a0 = 12`. `forget` replaces the old
/// write-a-constant-through-a-region trick (no region, no raw address), and it is
/// *sound*: the proof covers all values, of which the runtime value is one.
///
/// This is how the fannkuch programs keep the verifier from unrolling the search
/// around a known `n`. The `#~ a0` is dropped from the binary; it lowers to a
/// hosted ELF and runs under `qemu-riscv64`, exiting cleanly.
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
    // `forget` is verifier-only: the havoc directive must not appear in the binary.
    assert!(
        !asm.contains("#~"),
        "the `forget` directive must not be emitted:\n{asm}"
    );
    bless_asm(
        "runtime_input/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("runtime_input", &asm);
    assert_eq!(stdout, "", "runtime_input exits cleanly with no output");
}
