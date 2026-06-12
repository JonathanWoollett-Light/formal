mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Full UART "Hello, World!" with runtime list-type checking (`#&`/lat). The
/// verifier infers `value: (Global, U32)` and `welcome: (Thread({0}),
/// List([U8, U8]))`, then dead-code/dead-branch elimination reduces the program
/// to its straight-line writer loop.
#[test]
fn three() {
    let mut ast = setup_test("three");

    // The parsed + compressed AST round-trips to its canonical form.
    let expected = normalize(include_str!("../assets/three_ast.s"));
    assert_eq!(normalize(print_ast(ast)), expected);

    // The QEMU `virt` UART MMIO region.
    let sections = vec![Section {
        address: MemoryValueI64::from(0x10000000),
        size: MemoryValueI64::from(1),
        permissions: Permissions::Write,
        volatile: true,
    }];
    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[
                InnerVerifierConfiguration {
                    sections: sections.clone(),
                    harts: 1,
                },
                InnerVerifierConfiguration {
                    sections: sections.clone(),
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
    } = expect_valid(&trace, result);

    // Exact number of state-machine steps to reach the valid path. (Its full
    // per-step trace is ~20k lines; the per-step interleaving/inference shape is
    // pinned in detail by `four`/`five`/`six`.)
    assert_eq!(trace.len(), 20464);

    // Exact type-inference timeline: `value` is searched `Gu8` → … → `Gu32`,
    // then `welcome`'s explicitly-declared `[u8 u8]` list type joins the config.
    // The first step is now the `#$` define (no `_start:` entry), so the search
    // opens directly on `Gu8`.
    assert_eq!(
        config_timeline(&trace),
        [
            "Config: [value:Gu8,]",
            "Config: []",
            "Config: [value:Gi8,]",
            "Config: []",
            "Config: [value:Gu16,]",
            "Config: []",
            "Config: [value:Gi16,]",
            "Config: []",
            "Config: [value:Gu32,]",
            "Config: [value:Gu32,welcome:T[u8 u8],]",
        ]
    );

    // The inferred type configuration.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![
                (Label::from("value"), (LabelLocality::Global, Type::U32)),
                (
                    Label::from("welcome"),
                    (
                        LabelLocality::Thread(BTreeSet::from([0])),
                        Type::List(vec![Type::U8, Type::U8])
                    )
                )
            ]
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
        addi t1, t1, 1\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 4\n\
        bge t1, t2, _invalid\n\
        csrr t0, mhartid\n\
        bnez t0, _wait\n\
        #$ welcome _ [u8 u8]\n\
        #& t0, welcome\n\
        li t2, 8\n\
        ld t1, 0(t0)\n\
        bne t1, t2, _invalid\n\
        addi t0, t0, 16\n\
        ld t1, 0(t0)\n\
        li t2, 2\n\
        bne t1, t2, _invalid\n\
        addi t0, t0, -8\n\
        ld t0, 0(t0)\n\
        li t5, 0\n\
        _check_item:\n\
        beq t5, t2, _no_items\n\
        ld t3, 0(t0)\n\
        li t4, 0\n\
        bne t3, t4, _invalid\n\
        addi t0, t0, 25\n\
        addi t5, t5, 1\n\
        j _check_item\n\
        _no_items:\n\
        la t0, welcome\n\
        li t1, 72\n\
        sb t1, 0(t0)\n\
        li t1, 0\n\
        sb t1, 1(t0)\n\
        la a0, welcome\n\
        li t1, 0x10000000\n\
        _write_uart:\n\
        lb t2, 0(a0)\n\
        beqz t2, _wait\n\
        sb t2, 0(t1)\n\
        addi a0, a0, 1\n\
        j _write_uart\n\
        _wait:\n\
        wfi\n\
        #?\n\
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
        addi t1, t1, 1\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 4\n\
        csrr t0, mhartid\n\
        bnez t0, _wait\n\
        #$ welcome _ [u8 u8]\n\
        #& t0, welcome\n\
        li t2, 8\n\
        ld t1, 0(t0)\n\
        addi t0, t0, 16\n\
        ld t1, 0(t0)\n\
        li t2, 2\n\
        addi t0, t0, -8\n\
        ld t0, 0(t0)\n\
        li t5, 0\n\
        _check_item:\n\
        beq t5, t2, _no_items\n\
        ld t3, 0(t0)\n\
        li t4, 0\n\
        addi t0, t0, 25\n\
        addi t5, t5, 1\n\
        j _check_item\n\
        _no_items:\n\
        la t0, welcome\n\
        li t1, 72\n\
        sb t1, 0(t0)\n\
        li t1, 0\n\
        sb t1, 1(t0)\n\
        la a0, welcome\n\
        li t1, 0x10000000\n\
        _write_uart:\n\
        lb t2, 0(a0)\n\
        beqz t2, _wait\n\
        sb t2, 0(t1)\n\
        addi a0, a0, 1\n\
        j _write_uart\n\
        _wait:\n\
        wfi\n\
        #?\n\
    ";
    assert_eq!(normalize(print_ast(ast)), expected);
}
