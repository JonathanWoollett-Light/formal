mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Same program as `five`, but `value` is given an explicit type
/// (`#$ value global u32`) rather than inferred, so the verifier checks the
/// annotation instead of searching for a type. Verification starts from the
/// first line (no `_start:` entry). The full per-step trace pins the exact state
/// machine behaviour: the breadth-first walk over the 1- and 2-hart systems, the
/// racy `sw`/`lw` interleavings fanning the queue out to 6 leaves and draining it
/// to 0, and `jumped` staying 0 (the `bne` never jumps because `value == 0`).
#[test]
fn six() {
    let mut ast = setup_test("six");

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

    // Verify, pinning every single step of the state machine.
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
    } = expect_valid(&trace, result);

    let expected_trace = [
        "h0/1 | #$ value global u32 | Config: [value:Gu32,] | q2 t1 j0",
        "h0/2 | #$ value global u32 | Config: [value:Gu32,] | q2 t1 j0",
        "h0/1 | la t0, value | Config: [value:Gu32,] | q2 t2 j0",
        "h1/2 | la t0, value | Config: [value:Gu32,] | q2 t2 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu32,] | q2 t3 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu32,] | q2 t3 j0",
        "h0/1 | sw t1, 0(t0) | Config: [value:Gu32,] | q2 t4 j0",
        "h0/2 | la t0, value | Config: [value:Gu32,] | q2 t4 j0",
        "h0/1 | lw t1, 0(t0) | Config: [value:Gu32,] | q2 t5 j0",
        "h0/2 | li t1, 0 | Config: [value:Gu32,] | q3 t5 j0",
        "h0/1 | li t2, 0 | Config: [value:Gu32,] | q3 t6 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q4 t6 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q5 t6 j0",
        "h0/1 | bne t1, t2, _invalid | Config: [value:Gu32,] | q4 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q4 t7 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q5 t7 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q5 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q4 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q3 t7 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q2 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q1 t7 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q0 t7 j0",
    ];
    assert_trace(&trace, &expected_trace);

    // The inferred type configuration.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                .into_iter()
                .collect()
        )
    );

    // Remove untouched nodes (dead code).
    unsafe {
        remove_untouched(&mut ast, &touched);
    }
    let expected = "\
        #$ value global u32\n\
        la t0, value\n\
        li t1, 0\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 0\n\
        bne t1, t2, _invalid\n\
    ";
    assert_eq!(normalize(print_ast(ast)), expected);

    // Remove branches that never jump.
    unsafe {
        remove_branches(&mut ast, &jumped);
    }
    let expected = "\
        #$ value global u32\n\
        la t0, value\n\
        li t1, 0\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 0\n\
    ";
    assert_eq!(normalize(print_ast(ast)), expected);

    // The program accesses exactly the four bytes of `value: u32` at runtime.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 4)].into_iter().collect())]
            .into_iter()
            .collect()
    );

    // Pin the exact lowered program: optimized instructions, entry + halt loop,
    // `.bss` storage for `value`, and no `.data` (no compile-time-only data).
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ value global u32
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 0
__halt:
    wfi
    j __halt

.section .bss
    .balign 8
value:
    .zero 4
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU). The verifier does not (yet)
    // detect that all of `six` is dead code, so we boot whatever it emits; the
    // program halts in `wfi` with no output, so success is simply "ran with no CPU
    // fault". (Were the verifier complete, this would lower to an empty program
    // that falls straight into the halt loop.)
    let serial = unsafe { run_program("six", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "six produces no UART output");
}
