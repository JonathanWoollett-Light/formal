mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Racy global store of `0` to `value` (type `_`, inferred), asserting
/// `value == 0` via `bne`. The full per-step trace below pins the exact state
/// machine behaviour, most notably the **type search**: `value` is tried as
/// `Gu8`, the word-sized `sw` overruns the 1-byte type so the path is invalid
/// and the configuration resets to `[]` (step 8); the search then backtracks
/// through `Gi8`, `Gu16`, `Gi16` (each failing at the `sw`, steps 18/27/36)
/// before `Gu32` holds (step 45) and exploration proceeds through the 2-hart
/// interleavings, fanning the queue out to 6 leaves and draining it to 0.
/// `jumped` stays 0 (the not-equal branch never jumps).
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
    } = expect_valid(&trace, result);

    let expected_trace = [
        "h0/1 | _start: | Config: [] | q2 t1 j0",
        "h0/2 | _start: | Config: [] | q2 t1 j0",
        "h0/1 | #$ value global _ | Config: [value:Gu8,] | q2 t2 j0",
        "h1/2 | #$ value global _ | Config: [value:Gu8,] | q2 t2 j0",
        "h0/1 | la t0, value | Config: [value:Gu8,] | q2 t3 j0",
        "h1/2 | la t0, value | Config: [value:Gu8,] | q2 t3 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu8,] | q2 t4 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu8,] | q2 t4 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t5 j0",
        "h0/1 | _start: | Config: [] | q2 t5 j0",
        "h0/2 | _start: | Config: [] | q2 t5 j0",
        "h0/1 | #$ value global _ | Config: [value:Gi8,] | q2 t5 j0",
        "h1/2 | #$ value global _ | Config: [value:Gi8,] | q2 t5 j0",
        "h0/1 | la t0, value | Config: [value:Gi8,] | q2 t5 j0",
        "h1/2 | la t0, value | Config: [value:Gi8,] | q2 t5 j0",
        "h0/1 | li t1, 0 | Config: [value:Gi8,] | q2 t5 j0",
        "h1/2 | li t1, 0 | Config: [value:Gi8,] | q2 t5 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t5 j0",
        "h0/1 | _start: | Config: [] | q2 t5 j0",
        "h0/2 | _start: | Config: [] | q2 t5 j0",
        "h0/1 | #$ value global _ | Config: [value:Gu16,] | q2 t5 j0",
        "h1/2 | #$ value global _ | Config: [value:Gu16,] | q2 t5 j0",
        "h0/1 | la t0, value | Config: [value:Gu16,] | q2 t5 j0",
        "h1/2 | la t0, value | Config: [value:Gu16,] | q2 t5 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu16,] | q2 t5 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu16,] | q2 t5 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t5 j0",
        "h0/1 | _start: | Config: [] | q2 t5 j0",
        "h0/2 | _start: | Config: [] | q2 t5 j0",
        "h0/1 | #$ value global _ | Config: [value:Gi16,] | q2 t5 j0",
        "h1/2 | #$ value global _ | Config: [value:Gi16,] | q2 t5 j0",
        "h0/1 | la t0, value | Config: [value:Gi16,] | q2 t5 j0",
        "h1/2 | la t0, value | Config: [value:Gi16,] | q2 t5 j0",
        "h0/1 | li t1, 0 | Config: [value:Gi16,] | q2 t5 j0",
        "h1/2 | li t1, 0 | Config: [value:Gi16,] | q2 t5 j0",
        "h0/1 | sw t1, 0(t0) | Config: [] | q2 t5 j0",
        "h0/1 | _start: | Config: [] | q2 t5 j0",
        "h0/2 | _start: | Config: [] | q2 t5 j0",
        "h0/1 | #$ value global _ | Config: [value:Gu32,] | q2 t5 j0",
        "h1/2 | #$ value global _ | Config: [value:Gu32,] | q2 t5 j0",
        "h0/1 | la t0, value | Config: [value:Gu32,] | q2 t5 j0",
        "h1/2 | la t0, value | Config: [value:Gu32,] | q2 t5 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu32,] | q2 t5 j0",
        "h1/2 | li t1, 0 | Config: [value:Gu32,] | q2 t5 j0",
        "h0/1 | sw t1, 0(t0) | Config: [value:Gu32,] | q2 t5 j0",
        "h0/2 | #$ value global _ | Config: [value:Gu32,] | q2 t5 j0",
        "h0/1 | lw t1, 0(t0) | Config: [value:Gu32,] | q2 t6 j0",
        "h0/2 | la t0, value | Config: [value:Gu32,] | q2 t6 j0",
        "h0/1 | li t2, 0 | Config: [value:Gu32,] | q2 t7 j0",
        "h0/2 | li t1, 0 | Config: [value:Gu32,] | q3 t7 j0",
        "h0/1 | bne t1, t2, _invalid | Config: [value:Gu32,] | q2 t8 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q3 t8 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q4 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q4 t8 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q5 t8 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q5 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q4 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q3 t8 j0",
        "h0/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q2 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q1 t8 j0",
        "h1/2 | bne t1, t2, _invalid | Config: [value:Gu32,] | q0 t8 j0",
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
        _start:\n\
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
        _start:\n\
        #$ value global _\n\
        la t0, value\n\
        li t1, 0\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 0\n\
    ";
    assert_eq!(normalize(print_ast(ast)), expected);
}
