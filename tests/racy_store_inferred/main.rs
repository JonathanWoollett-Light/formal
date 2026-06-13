#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Racy global store of `0` to `value` (type `_`, inferred), asserting
/// `value == 0` with `require`, which lowers to `beq ..., _l0` branching over
/// the `#!` fail marker. The full per-step trace below pins the exact state
/// machine behaviour. Verification starts from the first line (there is no
/// `_start:` entry), so the first step is the `#$` define. Most notably it shows
/// the **type search**: `value` is tried as `Gu8`, the word-sized `sw` overruns
/// the 1-byte type so the path is invalid and the configuration resets to `[]`;
/// the search then backtracks through `Gi8`, `Gu16`, `Gi16` before `Gu32` holds
/// and exploration proceeds through the 2-hart interleavings, fanning the queue
/// out to 7 leaves and draining it to 0. The `beq` is always taken (the values
/// are proven equal, so the `#!` is unreachable), so `jumped` reaches 1.
#[test]
fn racy_store_inferred() {
    let mut ast = setup_test("racy_store_inferred/dialect.s");
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

    // Verify, pinning every single step of the state machine.
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
        "h0/1 | beq t1, t2, _l0 | Config: [value:Gu32,] | q5 t7 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q5 t7 j1",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t7 j1",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q7 t7 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q7 t7 j1",
        "h0/1 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | sw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | lw t1, 0(t0) | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | li t2, 0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h1/2 | beq t1, t2, _l0 | Config: [value:Gu32,] | q6 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q5 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q4 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q3 t8 j1",
        "h0/2 | _l0: | Config: [value:Gu32,] | q2 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q1 t8 j1",
        "h1/2 | _l0: | Config: [value:Gu32,] | q0 t8 j1",
    ];
    if !blessing() {
        assert_trace(&trace, &expected_trace);
    }

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
    bless_asm(
        "racy_store_inferred/untouched.s",
        print_ast(ast),
        include_str!("untouched.s"),
    );

    // Remove branches that never jump.
    unsafe {
        remove_branches(&mut ast, &jumped);
    }
    bless_asm(
        "racy_store_inferred/optimized.s",
        print_ast(ast),
        include_str!("optimized.s"),
    );

    // The program accesses exactly the four bytes of the inferred `value: u32` at
    // runtime (the `sw`/`lw` pair); this is what drives dead-data elimination.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 4)].into_iter().collect())]
            .into_iter()
            .collect()
    );

    // Pin the exact lowered program: the optimized instructions plus the entry and
    // halt loop, `.bss` storage for `value`, and **no `.data` at all**: nothing
    // here is read through a runtime type descriptor, so no compile-time
    // information (e.g. locality data) exists in the output.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "racy_store_inferred/emitted.s",
        asm,
        include_str!("emitted.s"),
    );

    // Boot it in QEMU (requires the toolchain + QEMU). It does racy arithmetic on
    // the inferred `value` and halts in `wfi` (no output), so success is simply
    // "ran with no CPU fault".
    let serial = unsafe {
        run_program(
            "racy_store_inferred",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "racy_store_inferred produces no UART output");
}
