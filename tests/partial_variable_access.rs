mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Only bytes 0 and 2 of a 4-byte list variable are accessed at runtime. The
/// recorded ranges are exactly those two bytes (the precision dead-data
/// trimming will rely on), while the `.bss` storage is still emitted at the
/// type's full 4 bytes — bytes that are merely *unaccessed* are never trimmed
/// from live variable storage.
#[test]
fn partial_access_records_exact_bytes_and_keeps_full_storage() {
    let mut ast = setup_test("partial_variable_access");

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

    // Exactly bytes 0 and 2 — not the whole variable.
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

    // `.bss` storage stays at the full type size: only *compile-time-only*
    // descriptor bytes are subject to dead-data elimination today.
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ data _ [u8 u8 u8 u8]
    la t0, data
    li t1, 7
    sb t1, 0(t0)
    lb t2, 2(t0)
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
data:
    .zero 4
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU) — no output, no fault.
    let serial = unsafe { run_program("partial_variable_access", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "partial_variable_access produces no UART output");
}
