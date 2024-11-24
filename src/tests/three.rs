use crate::verifier_types::*;
use crate::*;
use indicatif::{ProgressBar, ProgressStyle};
use std::collections::BTreeSet;

#[test]
fn three() {
    let (guard, mut ast, _asserter) = super::setup_test("three");

    let expected = include_str!("../../assets/three_ast.s");
    let actual = print_ast(ast);
    assert_eq!(actual, expected);

    let sections = vec![Section {
        address: MemoryValueI64::from(0x10000000),
        size: MemoryValueI64::from(1),
        permissions: Permissions::Write,
        volatile: true,
    }];
    let mut explorerer = unsafe {
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
    };

    let style = ProgressStyle::with_template(
        "{bar:40} {pos:>7}/{len:>7} [{elapsed_precise} / {eta_precise}] {msg}",
    )
    .unwrap();

    // Find valid path.
    let ValidPathResult {
        configuration,
        touched,
        jumped,
    } = unsafe {
        const N: u64 = 20477;
        let bar = ProgressBar::new(N)
            .with_style(style.clone())
            .with_message("verifiying program");
        for i in 0..N {
            explorerer = explorerer.next_step().continued().expect(&format!("{i}"));
            bar.inc(1);
        }
        bar.finish();
        explorerer.next_step().valid().unwrap()
    };

    // Optimize based on path.
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

    // Remove untouched nodes.
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
        addi t1, t1, 1\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 4\n\
        bge t1, t2, _invalid\n\
        csrr t0, mhartid\n\
        bnez t0, _wait\n\
        #$ welcome _ [u8 u8]\n\
        lat t0, welcome\n\
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
        branch _check_item\n\
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
    let actual = print_ast(ast);
    assert_eq!(actual, expected);

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
        addi t1, t1, 1\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 4\n\
        csrr t0, mhartid\n\
        bnez t0, _wait\n\
        #$ welcome _ [u8 u8]\n\
        lat t0, welcome\n\
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
        branch _check_item\n\
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
    let actual = print_ast(ast);
    assert_eq!(actual, expected);

    drop(guard);
}
