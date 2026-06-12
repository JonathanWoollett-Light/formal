mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Heap accesses through `#@` region declarations. The program declares one
/// region with immediate bounds (accessed at a non-zero offset) and one through
/// registers (the way an allocator would declare each allocation just before
/// returning its pointer — and exactly as wide as the store that hits it), then
/// stores/loads through raw addresses inside them. The declarations are
/// compile-time metadata, but their *order* matters — a region is accessible
/// only after its declaration executes — so `#@` is treated as racy and every
/// interleaving against the (racy) raw accesses is explored. Codegen lowers
/// `#@` to a comment: the output program needs no `.data`/`.bss` at all.
#[test]
fn heap_regions() {
    let mut ast = setup_test("heap_regions");

    // The parsed + compressed AST round-trips, including both `#@` forms.
    let source = "\
        #@ 0x80100000 0x80100008 rw\n\
        li t0, 0x80100000\n\
        li t1, 42\n\
        sw t1, 4(t0)\n\
        lw t2, 4(t0)\n\
        li t3, 0x80200000\n\
        li t4, 0x80200004\n\
        #@ t3 t4 rw\n\
        sw t1, 0(t3)\n\
        lw t5, 0(t3)\n\
        #?\n\
    ";
    assert_eq!(normalize(print_ast(ast)), source);

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

    // Verify, capturing the per-step trace.
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
    } = expect_valid(&trace, result);

    // Exact number of state-machine steps to validate every interleaving of the
    // racy `#@` declarations and raw accesses across the harts.
    assert_eq!(trace.len(), 1021);

    // No variables: nothing to infer, and raw (non-label) accesses do not appear
    // in the accessed-ranges (they have no generated storage to trim).
    assert_eq!(configuration, TypeConfiguration(Default::default()));
    assert_eq!(accessed, Default::default());

    // Only the final `#?` is dropped (the harts halt before it, so it is never
    // touched); nothing branches, so the rest survives unchanged.
    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }
    let optimized = "\
        #@ 0x80100000 0x80100008 rw\n\
        li t0, 0x80100000\n\
        li t1, 42\n\
        sw t1, 4(t0)\n\
        lw t2, 4(t0)\n\
        li t3, 0x80200000\n\
        li t4, 0x80200004\n\
        #@ t3 t4 rw\n\
        sw t1, 0(t3)\n\
        lw t5, 0(t3)\n\
    ";
    assert_eq!(normalize(print_ast(ast)), optimized);

    // Pin the exact lowered program: `#@` survives only as a comment, execution
    // falls into the appended halt loop, and there is no `.data`/`.bss` — the
    // regions are heap, not generated storage.
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #@ 0x80100000 0x80100008 rw
    li t0, 0x80100000
    li t1, 42
    sw t1, 4(t0)
    lw t2, 4(t0)
    li t3, 0x80200000
    li t4, 0x80200004
    #@ t3 t4 rw
    sw t1, 0(t3)
    lw t5, 0(t3)
__halt:
    wfi
    j __halt
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU). The stores land in RAM
    // (0x80100004/0x80200000 on the `virt` machine), the loads read them back,
    // and the program halts — no output, no CPU fault.
    let serial = unsafe { run_program("heap_regions", ast, &configuration, &accessed) };
    assert_eq!(serial, "", "heap_regions produces no UART output");
}
