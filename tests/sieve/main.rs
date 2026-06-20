#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// Sieve of Eratosthenes proven correct at compile time: the verifier runs the
/// whole sieve over concrete indices, so the closing `require a2 == 10` is only
/// reachable-as-satisfied if the program really counts the ten primes below 30.
/// A genuine little program (a `[u8]` flag array, pointer-indexed loads/stores,
/// nested `while` loops, `if flags[i] == 0`), it exercises the verifier's
/// array model and the `bge`/`bnez` branch resolution end to end, then boots
/// under `qemu-riscv64` and exits 0 with no output.
#[test]
fn sieve() {
    let mut ast = setup_test("sieve/dialect.s");
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
    bless_asm("sieve/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("sieve", &asm);
    assert_eq!(
        stdout, "",
        "the sieve computes and exits cleanly with no output"
    );
}
