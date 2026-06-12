mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// A 4-byte store at offset 2: the access needs a type at least 6 bytes wide,
/// so the search rejects `u8`/`i8`/`u16`/`i16`/`u32`/`i32` (each fails the
/// bounds check at the `sw`) and lands on `u64` — the *offset* participates in
/// type inference, not just the access width. The recorded range covers
/// exactly bytes 2..6.
#[test]
fn store_offset_widens_inferred_type() {
    let mut ast = setup_test("offset_widened_inference");

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

    // Exact number of state-machine steps for the six failed candidates plus
    // the successful u64 exploration.
    assert_eq!(trace.len(), 29);

    // The type search walks every too-small candidate before u64 holds.
    assert_eq!(
        config_timeline(&trace),
        [
            "Config: [value:Gu8,]",
            "Config: []",
            "Config: [value:Gi8,]",
            "Config: []",
            "Config: [value:Gu16,]",
            "Config: []",
            "Config: [value:Gi16,]",
            "Config: []",
            "Config: [value:Gu32,]",
            "Config: []",
            "Config: [value:Gi32,]",
            "Config: []",
            "Config: [value:Gu64,]",
        ]
    );

    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U64))]
                .into_iter()
                .collect()
        )
    );

    // Exactly bytes 2..6 of the inferred u64.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), BTreeSet::from([(2, 6)]))]
            .into_iter()
            .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // Storage compacts to the four accessed bytes (2..6 of the inferred u64),
    // with both accesses re-pointed from offset 2 to 0.
    let asm = emit_executable(ast, &configuration, &accessed, &transitions, &uncompactable, &pinned_nodes);
    let expected = ".global _start
_start:
    #$ value global _
    la t0, value
    li t1, 7
    sw t1, 0(t0)
    lw t2, 0(t0)
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU) — no output, no fault.
    let serial = unsafe { run_program("offset_widened_inference", ast, &configuration, &accessed, &transitions, &uncompactable, &pinned_nodes) };
    assert_eq!(serial, "", "offset_widened_inference produces no UART output");
}
