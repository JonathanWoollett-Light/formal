use crate::verifier_types::*;
use crate::*;
use tracing::info;

#[test]
fn three() {
    let (guard, mut ast, asserter) = super::setup_test("three");

    let mut explorerer = unsafe { Explorerer::new(ast, 1..3) };

    // Find valid path.
    let ValidPathResult {
        configuration,
        touched,
        jumped,
    } = unsafe {
        for _ in 0..200 {
            explorerer = explorerer.next_step().continued().unwrap();
        }
        explorerer.next_step().valid().unwrap()
    };

    // Optimize based on path.
    assert_eq!(
        configuration,
        ProgramConfiguration(
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
