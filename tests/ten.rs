mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// A descriptor load that is the **last instruction before `#?`** on its only
/// path. State replays exclude the instruction being processed, and a `#?`
/// successor enqueues nothing — so this load is never interior to any replay.
/// Its bytes reach `accessed` only through the explicit check-time record in
/// `check_load`; without it, dead-data elimination would emit `__value_type`
/// with **zero** data bytes while the program still `ld`s 8 of them at runtime
/// (a wrong program, not a test failure). This test pins that the bytes are
/// recorded and emitted.
#[test]
fn path_terminal_access_is_recorded() {
    let mut ast = setup_test("ten");

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
    } = expect_valid(&trace, result);

    let expected_trace = [
        "h0/1 | #$ value global u32 | Config: [value:Gu32,] | q1 t1 j0",
        "h0/1 | #& t0, value | Config: [value:Gu32,] | q1 t2 j0",
        "h0/1 | li t5, 0 | Config: [value:Gu32,] | q1 t3 j0",
        "h0/1 | ld t1, 0(t0) | Config: [value:Gu32,] | q0 t4 j0",
    ];
    assert_trace(&trace, &expected_trace);

    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                .into_iter()
                .collect()
        )
    );

    // The terminal load's bytes ARE recorded: the descriptor's type-number field.
    assert_eq!(
        accessed,
        vec![(
            Label::from("__value_type"),
            BTreeSet::from([(0, 8)])
        )]
        .into_iter()
        .collect()
    );

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    // The emitted descriptor keeps the 8 bytes the program loads at runtime
    // (and only those — the ptr/length/locality fields are compile-time-only).
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ value global u32
    la t0, __value_type  # #& t0, value
    li t5, 0
    ld t1, 0(t0)
__halt:
    wfi
    j __halt

.section .data
__value_type:
    .dword 4

.section .bss
    .balign 8
value:
    .zero 4
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU): the load reads the
    // emitted descriptor bytes and the program halts — no output, no fault.
    let serial = unsafe { run_program("ten", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "ten produces no UART output");
}
