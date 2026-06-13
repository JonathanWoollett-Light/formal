#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Hart 0 reads the descriptor's type-number (bytes 0..8); hart 1 reads its
/// length (bytes 16..24). The accessed ranges are the **union over all harts
/// and paths**, so both fields must survive in `.data`: the subtypes-ptr
/// field between them becomes interior `.zero` padding, and the subtypes
/// array (never dereferenced on any path) is emitted with no bytes at all.
#[test]
fn descriptor_reads_union_across_harts() {
    let mut ast = setup_test("descriptor_read_union/dialect.s");
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

    // Exact number of state-machine steps.
    if !blessing() {
        assert_eq!(trace.len(), 46);
    }

    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(
                Label::from("welcome"),
                (
                    LabelLocality::Thread(BTreeSet::from([0, 1])),
                    Type::List(vec![Type::U8, Type::U8])
                )
            )]
            .into_iter()
            .collect()
        )
    );

    // The union of hart 0's read (0..8) and hart 1's read (16..24); the
    // subtypes array is never read on any path, so it has no entry.
    assert_eq!(
        accessed,
        vec![(
            Label::from("__welcome_type"),
            BTreeSet::from([(0, 8), (16, 24)])
        )]
        .into_iter()
        .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // Both read fields are emitted back to back (the unread subtypes-ptr field
    // between them is removed and hart 1's length read re-pointed from offset 16
    // to 8), and the never-read subtypes array and `welcome` storage contribute
    // zero bytes.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "descriptor_read_union/emitted.s",
        asm,
        include_str!("emitted.s"),
    );

    // Boot it in QEMU (requires the toolchain + QEMU): QEMU's single hart takes
    // the hart-0 path, reads the emitted type-number, and halts: no output.
    let serial = unsafe {
        run_program(
            "descriptor_read_union",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "descriptor_read_union produces no UART output");
}
