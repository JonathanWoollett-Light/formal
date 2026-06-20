#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// **fannkuch-redux V2**: multi-threaded (3 harts) + inline assembly, bare metal.
///
/// Three harts boot at the same entry and read `mhartid`. The symbolic hart-id
/// model guarantees only that exactly one reads 0 and the ids are unique (they
/// could be `[0, 15, 7]`), so the program uses the one distinction the verifier
/// can make -- `mhartid == 0` -- to elect a single leader; every other hart parks
/// on an inline-asm `wfi`. The verifier proves this for a **3-hart** configuration.
/// The workers do no shared work, so their non-racy steps collapse and only the
/// leader's thread-local fannkuch is explored. (`n` is kept small because the
/// leader runs a long stretch while the workers sit parked far back, which is the
/// O(N^2) worst case for the front-search; see the DEVELOPMENT.md note.)
///
/// The leader reads `n` at runtime (`forget`+`assume`), computes fannkuch(n), and
/// writes the checksum and max flip count to the QEMU virt UART (0x10000000) as
/// decimal -- bare metal, no `ecall`. Booted under QEMU; the UART receives
/// `2\n2\n` (the fannkuch(3) answer).
#[test]
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

    let serial = unsafe {
        run_program(
            "fannkuch_v2",
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
        "2\n2",
        "fannkuch(3): checksum 2, max flips 2"
    );
}
