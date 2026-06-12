mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Racy global store of `0` to `value` (type `_`, inferred), asserting
/// `value == 0` via `bne`. The full per-step trace below pins the exact state
/// machine behaviour. Verification starts from the first line (there is no
/// `_start:` entry), so the first step is the `#$` define. Most notably it shows
/// the **type search**: `value` is tried as `Gu8`, the word-sized `sw` overruns
/// the 1-byte type so the path is invalid and the configuration resets to `[]`;
/// the search then backtracks through `Gi8`, `Gu16`, `Gi16` before `Gu32` holds
/// and exploration proceeds through the 2-hart interleavings, fanning the queue
/// out to 6 leaves and draining it to 0. `jumped` stays 0 (the not-equal branch
/// never jumps).
#[test]
fn five() {
    let mut ast = setup_test("five");

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
        "h0/1 | #$ value global _ | Config: [value:Gu8,] | q2 t1 j0",
        "h0/2 | #$ value global _ | Config: [value:Gu8,] | q2 t1 j0",
        "h0/1 | la t0, value | Config: [value:Gu8,] | q2 t2 j0",
        "h1/2 | la t0, value | Config: [value:Gu8,] | q2 t2 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu8,] | q2 t3 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu8,] | q2 t3 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t4 j0",
        "h0/1 | #$ value global _ | Config: [value:Gi8,] | q2 t4 j0",
        "h0/2 | #$ value global _ | Config: [value:Gi8,] | q2 t4 j0",
        "h0/1 | la t0, value | Config: [value:Gi8,] | q2 t4 j0",
        "h1/2 | la t0, value | Config: [value:Gi8,] | q2 t4 j0",
        "h0/1 | li t1, 0 | Config: [value:Gi8,] | q2 t4 j0",
        "h1/2 | li t1, 0 | Config: [value:Gi8,] | q2 t4 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t4 j0",
        "h0/1 | #$ value global _ | Config: [value:Gu16,] | q2 t4 j0",
        "h0/2 | #$ value global _ | Config: [value:Gu16,] | q2 t4 j0",
        "h0/1 | la t0, value | Config: [value:Gu16,] | q2 t4 j0",
        "h1/2 | la t0, value | Config: [value:Gu16,] | q2 t4 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu16,] | q2 t4 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu16,] | q2 t4 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t4 j0",
        "h0/1 | #$ value global _ | Config: [value:Gi16,] | q2 t4 j0",
        "h0/2 | #$ value global _ | Config: [value:Gi16,] | q2 t4 j0",
        "h0/1 | la t0, value | Config: [value:Gi16,] | q2 t4 j0",
        "h1/2 | la t0, value | Config: [value:Gi16,] | q2 t4 j0",
        "h0/1 | li t1, 0 | Config: [value:Gi16,] | q2 t4 j0",
        "h1/2 | li t1, 0 | Config: [value:Gi16,] | q2 t4 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t4 j0",
        "h0/1 | #$ value global _ | Config: [value:Gu32,] | q2 t4 j0",
        "h0/2 | #$ value global _ | Config: [value:Gu32,] | q2 t4 j0",
        "h0/1 | la t0, value | Config: [value:Gu32,] | q2 t4 j0",
        "h1/2 | la t0, value | Config: [value:Gu32,] | q2 t4 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu32,] | q2 t4 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu32,] | q2 t4 j0",
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
        #$ value global _\n\
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
        #$ value global _\n\
        la t0, value\n\
        li t1, 0\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 0\n\
    ";
    assert_eq!(normalize(print_ast(ast)), expected);

    // The program accesses exactly the four bytes of the inferred `value: u32` at
    // runtime (the `sw`/`lw` pair) — this is what drives dead-data elimination.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 4)].into_iter().collect())]
            .into_iter()
            .collect()
    );

    // Pin the exact lowered program: the optimized instructions plus the entry and
    // halt loop, `.bss` storage for `value`, and **no `.data` at all** — nothing
    // here is read through a runtime type descriptor, so no compile-time
    // information (e.g. locality data) exists in the output.
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ value global _
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

    // Boot it in QEMU (requires the toolchain + QEMU). It does racy arithmetic on
    // the inferred `value` and halts in `wfi` — no output — so success is simply
    // "ran with no CPU fault".
    let serial = unsafe { run_program("five", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "five produces no UART output");
}
