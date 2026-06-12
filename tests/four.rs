mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Racy global increment of `value` (type `_`, inferred), asserting `value < 4`.
///
/// `four` has two racy stores plus the non-atomic increment, so its full
/// interleaving fan-out is large (614 steps — too many to assert line-for-line,
/// so the per-step interleaving shape is pinned by `five`/`six`). We pin the
/// exact total step count, the **type-inference timeline** (`value` searched
/// `Gu8` → `Gi8` → `Gu16` → `Gi16` → `Gu32`, with a reset to `[]` on each
/// failing `sw`), and the optimized output.
#[test]
fn four() {
    let mut ast = setup_test("four");

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
    } = expect_valid(&trace, result);

    // Exact number of state-machine steps to reach the valid path.
    assert_eq!(trace.len(), 603);

    // Exact type-inference timeline. The first step is now the `#$` define (the
    // program has no `_start:` entry), so the search opens directly on `Gu8`.
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
        ]
    );

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
        addi t1, t1, 1\n\
        sw t1, 0(t0)\n\
        lw t1, 0(t0)\n\
        li t2, 4\n\
        bge t1, t2, _invalid\n\
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
    ";
    assert_eq!(normalize(print_ast(ast)), expected);
}
