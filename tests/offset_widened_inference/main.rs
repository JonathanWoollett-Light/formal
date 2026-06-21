#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// A 4-byte store at offset 2: the access needs a type at least 6 bytes wide,
/// so the search rejects `u8`/`i8`/`u16`/`i16`/`u32`/`i32` (each fails the
/// bounds check at the `sw`) and lands on `u64`: the *offset* participates in
/// type inference, not just the access width. The recorded range covers
/// exactly bytes 2..6.
#[test]
fn store_offset_widens_inferred_type() {
    let mut ast = setup_test("offset_widened_inference/dialect.s");
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

    // Exact number of state-machine steps for the six failed candidates plus
    // the successful u64 exploration (and the closing `exit(0)`).
    if !blessing() {
        assert_eq!(trace.len(), 32);
    }

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
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "offset_widened_inference/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    // Run it as a hosted Linux program under `qemu-riscv64` (the hosted-Linux
    // stream): it computes and exits cleanly with no output.
    let stdout = run_linux("offset_widened_inference", &asm);
    assert_eq!(
        stdout, "",
        "offset_widened_inference computes and exits cleanly with no output"
    );
}
