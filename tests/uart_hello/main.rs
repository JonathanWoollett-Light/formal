#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// Full UART "Hello World!" with runtime list-type checking (`#&`/lat). The
/// verifier infers `value: (Global, U32)` and `welcome: (Thread({0}),
/// List([U8; 13]))`, dead-code/dead-branch elimination reduces the program to
/// its straight-line writer loop, and layout compaction removes every
/// descriptor byte the program does not read at runtime, rewriting the
/// record-walking stride from the source's 25 to the compacted 8 in lockstep.
///
/// Expected assembly lives beside this file: `ast.s` (the canonical
/// parsed/compressed form) and `untouched.s`/`optimized.s`/`emitted.s` (the
/// optimized and emitted stages), so it gets proper assembly syntax
/// highlighting.
#[test]
fn uart_hello() {
    let mut ast = setup_test("uart_hello/dialect.s");
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // The parsed + compressed AST round-trips to its canonical form.
    bless_asm("uart_hello/ast.s", print_ast(ast), include_str!("ast.s"));

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
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    } = expect_valid(&trace, result);

    // Exact number of state-machine steps to reach the valid path: the racy
    // UART writes interleave against the second hart across every ordering.
    if !blessing() {
        assert_eq!(trace.len(), 2111465);
    }

    // Exact type-inference timeline: `value` is searched `Gu8` → … → `Gu32`,
    // then `welcome`'s explicitly-declared 13-byte list type joins the config.
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
            "Config: [value:Gu32,welcome:T[u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8 u8],]",
        ]
    );

    // The inferred type configuration: a 13-byte u8 list ("Hello World!\0").
    let message_type = Type::List(vec![Type::U8; 13]);
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![
                (Label::from("value"), (LabelLocality::Global, Type::U32)),
                (
                    Label::from("welcome"),
                    (
                        LabelLocality::Thread(BTreeSet::from([0])),
                        message_type.clone()
                    )
                )
            ]
            .into_iter()
            .collect()
        )
    );

    // The byte ranges the program was proven to access at runtime. Note what is
    // *absent*: byte 24 of `__welcome_type` and each subtype record's
    // ptr/length/locality fields: bytes the program only consults through the
    // verifier at compile time, whose values are removed from the output.
    assert_eq!(
        accessed,
        vec![
            (
                Label::from("__welcome_subtypes"),
                // The check loop reads each record's type-number at the source's
                // 25-byte stride.
                (0..13u64)
                    .map(|record| (25 * record, 25 * record + 8))
                    .collect()
            ),
            (
                Label::from("__welcome_type"),
                [(0, 8), (8, 16), (16, 24)].into_iter().collect()
            ),
            (Label::from("value"), [(0, 4)].into_iter().collect()),
            (
                Label::from("welcome"),
                // Every byte of the message is written and read back.
                (0..13u64).map(|byte| (byte, byte + 1)).collect()
            ),
        ]
        .into_iter()
        .collect()
    );

    // Remove untouched nodes (dead code).
    unsafe {
        remove_untouched(&mut ast, &touched);
    }
    bless_asm(
        "uart_hello/untouched.s",
        print_ast(ast),
        include_str!("untouched.s"),
    );

    // Remove branches that never jump.
    unsafe {
        remove_branches(&mut ast, &jumped);
    }
    bless_asm(
        "uart_hello/optimized.s",
        print_ast(ast),
        include_str!("optimized.s"),
    );

    // Pin the exact lowered program. The headline is layout compaction: each
    // descriptor record's unread ptr/length/locality fields simply don't exist
    // in `.data`; `__welcome_type` is 24 bytes and `__welcome_subtypes` 104
    // (13 type-number `.dword`s instead of 13 padded 25-byte records), and the
    // record-walking loop is rewritten `addi t0, t0, 25` → `addi t0, t0, 8` to
    // match. No `.zero` padding and no `.byte` (locality) survive anywhere.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm("uart_hello/emitted.s", asm, include_str!("emitted.s"));

    // Boot it in QEMU (requires the toolchain + QEMU). Hart 0 writes the
    // message to the UART, so success is "ran with no CPU fault and the UART
    // received the full string".
    let serial = unsafe {
        run_program(
            "uart_hello",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(
        serial, "Hello World!",
        "uart_hello should write \"Hello World!\" to the UART"
    );
}
