#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Same program as `racy_store_inferred`, but `value` is given an explicit type
/// (`#$ value global u32`) rather than inferred, so the verifier checks the
/// annotation instead of searching for a type. Verification starts from the
/// first line (no `_start:` entry). The full per-step trace pins the exact state
/// machine behaviour: the breadth-first walk over the 1- and 2-hart systems, the
/// racy `sw`/`lw` interleavings fanning the queue out to 7 leaves and draining it
/// to 0, and the `require`'s `beq` always jumping over the `#!` (so `jumped`
/// reaches 1, the values being proven equal).
#[test]
fn racy_store_annotated() {
    let mut ast = setup_test("racy_store_annotated/dialect.s");
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
        "racy_store_annotated/untouched.s",
        print_ast(ast),
        include_str!("untouched.s"),
    );

    // Remove branches that never jump.
    unsafe {
        remove_branches(&mut ast, &jumped);
    }
    bless_asm(
        "racy_store_annotated/optimized.s",
        print_ast(ast),
        include_str!("optimized.s"),
    );

    // The program accesses exactly the four bytes of `value: u32` at runtime.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 4)].into_iter().collect())]
            .into_iter()
            .collect()
    );

    // Pin the exact lowered program: optimized instructions, entry + halt loop,
    // `.bss` storage for `value`, and no `.data` (no compile-time-only data).
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "racy_store_annotated/emitted.s",
        asm,
        include_str!("emitted.s"),
    );

    // Boot it in QEMU (requires the toolchain + QEMU). The verifier does not (yet)
    // detect that all of `racy_store_annotated` is dead code, so we boot whatever it emits; the
    // program halts in `wfi` with no output, so success is simply "ran with no CPU
    // fault". (Were the verifier complete, this would lower to an empty program
    // that falls straight into the halt loop.)
    let serial = unsafe {
        run_program(
            "racy_store_annotated",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "racy_store_annotated produces no UART output");
}
