use crate::verifier_types::*;
use crate::*;
use indicatif::{ProgressBar, ProgressStyle};

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
        const N: u64 = 1_000_000;
        let bar = ProgressBar::new(N)
            .with_style(style.clone())
            .with_message("verifiying program");
        for _ in 0..N {
            explorerer = explorerer.next_step().continued().unwrap();
            bar.inc(1);
        }
        bar.finish();
        explorerer.next_step().valid().unwrap()
    };

    // Optimize based on path.
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
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
            sw t1, (t0)\n\
            lw t1, (t0)\n\
            addi t1, t1, 1\n\
            sw t1, (t0)\n\
            lw t1, (t0)\n\
            li t2, 4\n\
            bge t1, t2, _invalid\n\
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
            sw t1, (t0)\n\
            lw t1, (t0)\n\
            addi t1, t1, 1\n\
            sw t1, (t0)\n\
            lw t1, (t0)\n\
            li t2, 4\n\
        ";
    let actual = print_ast(ast);
    assert_eq!(actual, expected);

    drop(guard);
}
