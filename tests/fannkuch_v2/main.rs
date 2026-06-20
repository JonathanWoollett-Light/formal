#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// **fannkuch-redux V2**: multi-threaded (3 harts) + inline assembly, bare metal,
/// computing the full **n = 12** benchmark input.
///
/// Three harts boot at the same entry and read `mhartid`. The symbolic hart-id
/// model guarantees only that exactly one reads 0 and the ids are unique (they
/// could be `[0, 15, 7]`), so the program uses the one distinction the verifier
/// can make -- `mhartid == 0` -- to elect a single leader; every other hart parks
/// on an inline-asm `wfi`. The verifier proves this for a **3-hart** configuration.
/// `n` is read at runtime (= 12) but the verifier is blind to it (`forget`) and an
/// `assume` narrows it to 3, so the *verified* search stays small (the leader is a
/// long solo stretch -- the O(N^2) front-search case -- so the verified n is kept
/// down) while the runtime computes the real n = 12.
///
/// The arrays are initialised over **all 12 elements** with a literal bound so the
/// dead-data compaction keeps them full-sized; otherwise they would be sized to
/// the verified n = 3 and the runtime n = 12 would read past them (the bug behind
/// the earlier runtime failures). The leader computes fannkuch(12) and writes the
/// result to the QEMU virt UART (0x10000000) as decimal -- bare metal, no `ecall`.
/// Booted under QEMU with the long-compute config (normal TCG, no per-instruction
/// log; ~1-2 min for 479M permutations); the UART receives
/// `3968050\nPfannkuchen(12) = 65` -- the answer from the C reference.
///
/// **Gated `#[ignore]`**: computing 479M permutations under bare-metal
/// `qemu-system-riscv64` (full machine emulation, ~7x slower than the hosted
/// user-mode `qemu-riscv64`) takes ~10 minutes, too slow for the default suite.
/// Run it explicitly to verify the full n = 12 output:
/// `cargo nextest run --run-ignored all fannkuch_v2`.
#[test]
#[ignore = "n=12 is ~10 min under bare-metal QEMU; run with --run-ignored"]
fn fannkuch_v2() {
    let mut ast = setup_test("fannkuch_v2/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // The QEMU `virt` UART MMIO region.
    let sections = vec![Section {
        address: MemoryValueI64::from(0x10000000),
        size: MemoryValueI64::from(1),
        permissions: Permissions::Write,
        volatile: true,
    }];
    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: sections.clone(),
                harts: 3,
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

    let asm = emit_executable(
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

    // 3 harts, long-compute config (n = 12 is ~1-2 min of 479M permutations).
    let serial = unsafe {
        run_program_smp(
            "fannkuch_v2",
            3,
            true,
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(
        serial.trim_end_matches('\n'),
        "3968050\nPfannkuchen(12) = 65",
        "fannkuch(12): checksum 3968050, max flips 65"
    );
}
