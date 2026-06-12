mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// One `sb` node, two kinds of execution: iteration 1 stores through a
/// **pointer** into `value` (a recorded transition, offset 4), iteration 2
/// stores through a **raw address** into the `#@` region — an execution
/// invisible to the transition records. Compacting `value` to its single
/// accessed byte would re-point the shared instruction to offset 0 and silently
/// move the raw store to a different address, so the raw execution **pins** the
/// node to its original immediate and `value` falls back to the padded layout:
/// the emitted program keeps `sb t3, 4(t1)` and the full-size storage.
#[test]
fn mixed_pointer_and_raw_node_keeps_its_immediate() {
    let mut ast = setup_test("mixed_pointer_raw");

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

    // Exact number of state-machine steps (the search walks u8…i32 — each fails
    // the 1-byte store at offset 4 — before u64 holds).
    assert_eq!(trace.len(), 52);

    // The store at offset 4 needs at least 5 bytes, so the search lands on u64.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U64))]
                .into_iter()
                .collect()
        )
    );

    // Only byte 4 of `value` is accessed through the pointer (the raw accesses
    // target the `#@` region and are not recorded).
    assert_eq!(
        accessed,
        vec![(Label::from("value"), BTreeSet::from([(4, 5)]))]
            .into_iter()
            .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // The regression pin: despite `value` having a single accessed byte, the
    // mixed `sb` keeps `4(t1)` and the storage its full 8 bytes — compaction
    // backed off rather than corrupt the raw execution.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    let expected = ".global _start
_start:
    #$ value global _
    la t1, value
    li t3, 0
    #@ 0x80100000 0x80100010 rw
_loop:
    sb t3, 4(t1)
    li t1, 0x80100000
    addi t3, t3, 1
    li t4, 2
    blt t3, t4, _loop
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 8
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU): both stores land where
    // the proof put them, the loop exits, no output, no fault.
    let serial = unsafe {
        run_program(
            "mixed_pointer_raw",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "mixed_pointer_raw produces no UART output");
}
