#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;
use std::collections::BTreeSet;

/// The inverse of every other program: this one **reads the descriptor's
/// locality byte (offset 24) at runtime**, so the byte must survive in `.data`
/// (preceded by `.zero` padding for the unread fields). Dead-data elimination
/// removes only information consulted exclusively at compile time: what the
/// program actually reads is emitted.
///
/// Note this test cannot use `run_program` (whose no-`.byte` assertion encodes
/// "these programs never read locality at runtime"; this program exists to
/// violate exactly that), so it lowers and boots via `emit_executable` +
/// `run_in_qemu` directly.
#[test]
fn runtime_locality_read_keeps_the_byte() {
    let mut ast = setup_test("locality_runtime_read/dialect.s");
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
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

    let expected_trace = [
        "h0/1 | #$ x global u8 | Config: [x:Gu8,] | q1 t1 j0",
        "h0/1 | #& t0, x | Config: [x:Gu8,] | q1 t2 j0",
        "h0/1 | li t5, 0 | Config: [x:Gu8,] | q1 t3 j0",
        "h0/1 | lb t1, 24(t0) | Config: [x:Gu8,] | q0 t4 j0",
    ];
    assert_trace(&trace, &expected_trace);

    // Exactly the locality byte is accessed.
    assert_eq!(
        accessed,
        vec![(Label::from("__x_type"), BTreeSet::from([(24, 25)]))]
            .into_iter()
            .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // The locality byte is the *only* emitted descriptor byte: compaction
    // removes the 24 unread bytes before it and re-points the `lb` at offset 0.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    let expected = normalize(include_str!("emitted.s"));
    assert_eq!(normalize(&asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU): the program reads the
    // emitted locality byte and halts: no output, no fault.
    let outcome = run_in_qemu("locality_runtime_read", &asm);
    assert_eq!(
        outcome.faults, 0,
        "locality_runtime_read faulted in QEMU:\n{}",
        outcome.fault_log
    );
    assert_eq!(
        outcome.serial, "",
        "locality_runtime_read produces no UART output"
    );
}
