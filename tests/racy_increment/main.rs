#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// Racy global increment of `value` (type `_`, inferred), asserting `value < 4`.
///
/// `racy_increment` has two racy stores plus the non-atomic increment, so its full
/// interleaving fan-out is large (744 steps: too many to assert line-for-line,
/// so the per-step interleaving shape is pinned by `racy_store_inferred`/`racy_store_annotated`). We pin the
/// exact total step count, the **type-inference timeline** (`value` searched
/// `Gu8` -> `Gi8` -> `Gu16` -> `Gi16` -> `Gu32`, with a reset to `[]` on each
/// failing `sw`), and the optimized output. The closing `require value < 4`
/// lowers to `blt ..., _l0` over the `#!` marker.
#[test]
fn racy_increment() {
    let mut ast = setup_test("racy_increment/dialect.s");
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

    // Verify, capturing the per-step trace.
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

    // Exact number of state-machine steps to reach the valid path.
    if !blessing() {
        assert_eq!(trace.len(), 744);
    }

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
    bless_asm(
        "racy_increment/untouched.s",
        print_ast(ast),
        include_str!("untouched.s"),
    );

    // Remove branches that never jump.
    unsafe {
        remove_branches(&mut ast, &jumped);
    }
    bless_asm(
        "racy_increment/optimized.s",
        print_ast(ast),
        include_str!("optimized.s"),
    );

    // The program accesses exactly the four bytes of the inferred `value: u32` at
    // runtime (the racy `sw`/`lw` increment).
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
    bless_asm("racy_increment/emitted.s", asm, include_str!("emitted.s"));

    // Boot it in QEMU (requires the toolchain + QEMU). It does racy arithmetic on
    // the inferred `value` and halts in `wfi` (no output), so success is simply
    // "ran with no CPU fault".
    let serial = unsafe {
        run_program(
            "racy_increment",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "racy_increment produces no UART output");
}
