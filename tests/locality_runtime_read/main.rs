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
/// Note this program intentionally emits and reads a `.byte` (the locality), so
/// it cannot use `run_program` (whose no-`.byte` assertion encodes "these
/// programs never read locality at runtime"). It runs in the hosted-Linux stream
/// via `run_linux`, which boots the emitted program under `qemu-riscv64` without
/// that assertion.
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

    if !blessing() {
        let expected_trace = [
            "h0/1 | #$ x global u8 | Config: [x:Gu8,] | q1 t1 j0",
            "h0/1 | #& t0, x | Config: [x:Gu8,] | q1 t2 j0",
            "h0/1 | li t5, 0 | Config: [x:Gu8,] | q1 t3 j0",
            "h0/1 | lb t1, 24(t0) | Config: [x:Gu8,] | q1 t4 j0",
            "h0/1 | li a0, 0 | Config: [x:Gu8,] | q1 t5 j0",
            "h0/1 | li a7, 93 | Config: [x:Gu8,] | q1 t6 j0",
            "h0/1 | ecall | Config: [x:Gu8,] | q0 t7 j0",
        ];
        assert_trace(&trace, &expected_trace);
    }

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
    bless_asm(
        "locality_runtime_read/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // Run it as a hosted Linux program under `qemu-riscv64` (the hosted-Linux
    // stream): the program reads the emitted locality byte and exits cleanly
    // with no output.
    let stdout = run_linux("locality_runtime_read", &asm);
    assert_eq!(
        stdout, "",
        "locality_runtime_read computes and exits cleanly with no output"
    );
}
