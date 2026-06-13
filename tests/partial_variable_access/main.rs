#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Only bytes 0 and 2 of a 4-byte list variable are accessed at runtime. The
/// recorded ranges are exactly those two bytes, and layout compaction emits
/// exactly those two: the unaccessed bytes 1 and 3 are removed from `.bss` and
/// the byte-2 access is re-pointed at compacted offset 1.
#[test]
fn partial_access_compacts_storage_to_accessed_bytes() {
    let mut ast = setup_test("partial_variable_access/dialect.s");
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[
                InnerVerifierConfiguration {
                    sections: Default::default(),
                    harts: 1,
                },
                InnerVerifierConfiguration {
                    sections: Default::default(),
                    harts: 2,
                },
            ],
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

    // Exact number of state-machine steps (everything is thread-local, so the
    // 2-hart system never forks).
    assert_eq!(trace.len(), 14);

    // The list type is annotated; the locality is inferred as thread-local,
    // with a copy for every hart that touches it.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(
                Label::from("data"),
                (
                    LabelLocality::Thread(BTreeSet::from([0, 1])),
                    Type::List(vec![Type::U8, Type::U8, Type::U8, Type::U8])
                )
            )]
            .into_iter()
            .collect()
        )
    );

    // Exactly bytes 0 and 2, not the whole variable.
    assert_eq!(
        accessed,
        vec![(Label::from("data"), BTreeSet::from([(0, 1), (2, 3)]))]
            .into_iter()
            .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // `.bss` storage compacts to the two accessed bytes: the unaccessed bytes
    // 1 and 3 are removed and the byte-2 access is re-pointed at offset 1.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    let expected = normalize(include_str!("emitted.s"));
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU): no output, no fault.
    let serial = unsafe {
        run_program(
            "partial_variable_access",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(
        serial, "",
        "partial_variable_access produces no UART output"
    );
}
