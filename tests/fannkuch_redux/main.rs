#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// fannkuch-redux (the Benchmarks Game permutation/pancake-flip benchmark)
/// written in the Python dialect, for n = 5. The dialect has no multiply, no
/// register-register arithmetic, and no indexed addressing, so every array
/// access is a pointer walk and every reg+reg combine is a +/-1 loop; the whole
/// algorithm (generate all n! permutations, count flips, track max flips and the
/// alternating checksum) still lowers to ~120 instructions.
///
/// The distinguishing part: the two `require`s at the end assert the computed
/// `max flips == 7` and `checksum == 11` (the known fannkuch(5) answer), so the
/// verifier **proves the algorithm correct at compile time** -- the program is
/// only `Valid` if those hold on the single concrete execution it explores.
/// We then lower it to a static RISC-V ELF and **run it under `qemu-riscv64`**;
/// it computes and exits 0 with no output (the answer was already proven, so it
/// need not print anything).
#[test]
fn fannkuch_redux() {
    let mut ast = setup_test("fannkuch_redux/dialect.s");
    // The Python-like source translates exactly to the stored dialect.
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // A single hosted hart, no memory-mapped regions: the program reaches the
    // outside world only through the `exit` syscall (`ecall`), not a raw store.
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

    // Pin the exact lowered program, then build it into a static ELF and run it.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "fannkuch_redux/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // The result is proven at compile time (the two `require`s), so the program
    // just computes and exits 0 with no output.
    let stdout = run_linux("fannkuch_redux", &asm);
    assert_eq!(
        stdout, "",
        "fannkuch_redux computes and exits cleanly with no output"
    );
}
