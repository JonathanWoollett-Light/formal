#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **fannkuch-redux V2**: *real* parallel work-sharing across 2 harts, hosted Linux.
/// Both harts genuinely share the work (not a leader/worker split), each computing
/// into its OWN `perm`/`work`/`cnt` copies -- which the per-hart thread-local
/// storage codegen makes possible.
///
/// The n! permutations split into n contiguous blocks under the fannkuch rotation
/// enumeration, indexed by the top odometer digit. Block c is the (n-1)!
/// permutations whose whole array is rotated left c (first permutation
/// `perm[j] = (c+j) % n`), walked by the ordinary next-permutation rotation bounded
/// to the lower digits. Because (n-1)! is even for n >= 3, every block starts at
/// global parity 0, so a hart's per-block checksums (local parity also starting at
/// 0) simply ADD to the global checksum. Each hart claims a rank via `amoadd` and
/// takes blocks `rank, rank+2, ...`; the partials combine lock-free -- `amoadd`
/// into per-rank checksum slots and `amomax` into a shared max word -- and the last
/// finisher writes the result and halts the machine via the `sifive_test` finisher.
///
/// The verifier proves this for **2 harts** (3 is verification-infeasible) with `n`
/// narrowed to 3; the runtime computes the real **n = 12** and stdout must be
/// `3968050\nPfannkuchen(12) = 65` -- the fannkuch(12) reference answer, with the
/// work split across two harts. Correctness rides on the runtime output:
/// the verifier proves memory-safety and every 2-hart interleaving (and, with the
/// per-hart TLS lowering, that the harts use disjoint storage), but not the
/// arithmetic of the decomposition (that the partials reconstruct the serial sum).
///
/// Runs **hosted** under user-mode `qemu-riscv64`: the hosted codegen spawns the
/// second hart as an OS thread (`clone`), so the two harts run in parallel on two
/// cores -- far faster than `-smp` round-robin under full-system emulation.
///
/// Dropping the racy UART MMIO for `print` also collapsed verification from the
/// old ~3.5M steps (the MMIO stores were the interleaving explosion) to ~24k, so
/// only the n = 12 compute is now heavy (~36s plugin-free across two cores, vs
/// minutes bare-metal).
///
/// **Gated `#[ignore]`**: keeps the ~36s n = 12 run out of the default suite. Run
/// it explicitly: `cargo nextest run --run-ignored all fannkuch_v2`.
#[test]
#[ignore = "n=12 run is ~36s (hosted, 2 cores); run with --run-ignored"]
fn fannkuch_v2() {
    let mut ast = setup_test("fannkuch_v2/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // Hosted Linux: output is via `print` (the `write` syscall) and there is no
    // MMIO, so the verifier needs no sections. The two harts are proven exactly as
    // before; the hosted codegen then materializes them as OS threads.
    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts: 2,
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
    eprintln!("fannkuch_v2: {} verifier steps", trace.len());

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    let asm = emit_executable_hosted(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    assert!(
        !asm.contains("#~") && !asm.contains("#(") && !asm.contains("typeof"),
        "forget/assume/typeof must be resolved at compile time:\n{asm}"
    );
    bless_asm(
        "fannkuch_v2/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // Run hosted under user-mode qemu-riscv64: the program spawns a second OS
    // thread (the hosted codegen's `clone` prologue), so the two harts compute in
    // parallel -- the fastest way to run n = 12. `long`: heavy even split in two.
    let stdout = run_linux_opts("fannkuch_v2", &asm, true);
    assert_eq!(
        stdout.trim_end_matches('\n'),
        "3968050\nPfannkuchen(12) = 65",
        "fannkuch(12) combined across 2 harts: checksum 3968050, max flips 65"
    );
}
