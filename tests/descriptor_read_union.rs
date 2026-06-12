mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Hart 0 reads the descriptor's type-number (bytes 0..8); hart 1 reads its
/// length (bytes 16..24). The accessed ranges are the **union over all harts
/// and paths**, so both fields must survive in `.data` — the subtypes-ptr
/// field between them becomes interior `.zero` padding, and the subtypes
/// array (never dereferenced on any path) is emitted with no bytes at all.
#[test]
fn descriptor_reads_union_across_harts() {
    let mut ast = setup_test("descriptor_read_union");

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

    // Exact number of state-machine steps.
    assert_eq!(trace.len(), 43);

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

    // Both read fields are emitted, the unread field between them is padding,
    // and the never-read subtypes array contributes zero bytes.
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ welcome _ [u8 u8]
    csrr t0, mhartid
    bnez t0, _other
    la t1, __welcome_type  # #& t1, welcome
    li t5, 0
    ld t2, 0(t1)
    j _wait
_other:
    la t1, __welcome_type  # #& t1, welcome
    li t5, 0
    ld t2, 16(t1)
_wait:
    wfi
    j __halt  # unreachable (program end)
__halt:
    wfi
    j __halt

.section .data
__welcome_type:
    .dword 8                # List
    .zero 8                # never accessed at runtime (padding)
    .dword 2                # length
__welcome_subtypes:

.section .bss
    .balign 8
welcome:
    .zero 2
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU): QEMU's single hart takes
    // the hart-0 path, reads the emitted type-number, and halts — no output.
    let serial = unsafe { run_program("descriptor_read_union", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "descriptor_read_union produces no UART output");
}
