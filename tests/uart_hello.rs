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
fn uart_hello() {
    let mut ast = setup_test("uart_hello");

    // The parsed + compressed AST round-trips to its canonical form.
    let expected = normalize(include_str!("../assets/uart_hello_ast.s"));
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
        accessed,
    } = expect_valid(&trace, result);

    // Exact number of state-machine steps to reach the valid path. (Its full
    // per-step trace is ~20k lines; the per-step interleaving/inference shape is
    // pinned in detail by `racy_increment`/`racy_store_inferred`/`racy_store_annotated`.)
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

    // The byte ranges the program was proven to access at runtime. Note what is
    // *absent*: byte 24 of `__welcome_type` and bytes 8–25/33–50 of
    // `__welcome_subtypes` — each record's subtypes-ptr/length/locality fields the
    // program only consults through the verifier at compile time. Those bytes'
    // values are dead in the output (see the `.data` assertion below).
    assert_eq!(
        accessed,
        vec![
            (
                Label::from("__welcome_subtypes"),
                [(0, 8), (25, 33)].into_iter().collect()
            ),
            (
                Label::from("__welcome_type"),
                [(0, 8), (8, 16), (16, 24)].into_iter().collect()
            ),
            (Label::from("value"), [(0, 4)].into_iter().collect()),
            (
                Label::from("welcome"),
                [(0, 1), (1, 2)].into_iter().collect()
            ),
        ]
        .into_iter()
        .collect()
    );

    // Pin the exact lowered program. The headline is the `.data` section: the
    // descriptor bytes the program never reads at runtime are **not stored** —
    // each record's trailing locality byte vanishes (the program checks types via
    // `#&` at offsets 0/8/16 only), and the interior dead bytes of the subtypes
    // array survive only as `.zero` padding because the program strides the
    // records by their full 25 bytes. No `.byte` (locality) directive remains
    // anywhere in `.data`/`.bss`.
    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ value global _
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 4
    csrr t0, mhartid
    bnez t0, _wait
    #$ welcome _ [u8 u8]
    la t0, __welcome_type  # #& t0, welcome
    li t2, 8
    ld t1, 0(t0)
    addi t0, t0, 16
    ld t1, 0(t0)
    li t2, 2
    addi t0, t0, -8
    ld t0, 0(t0)
    li t5, 0
_check_item:
    beq t5, t2, _no_items
    ld t3, 0(t0)
    li t4, 0
    addi t0, t0, 25
    addi t5, t5, 1
    j _check_item
_no_items:
    la t0, welcome
    li t1, 72
    sb t1, 0(t0)
    li t1, 0
    sb t1, 1(t0)
    la a0, welcome
    li t1, 0x10000000
_write_uart:
    lb t2, 0(a0)
    beqz t2, _wait
    sb t2, 0(t1)
    addi a0, a0, 1
    j _write_uart
_wait:
    wfi
    j __halt  # unreachable (program end)
__halt:
    wfi
    j __halt

.section .data
__welcome_type:
    .dword 8                # List
    .dword __welcome_subtypes      # subtypes
    .dword 2                # length
__welcome_subtypes:
    .dword 0
    .zero 17                # never accessed at runtime (padding)
    .dword 0

.section .bss
    .balign 8
value:
    .zero 4
    .balign 8
welcome:
    .zero 2
";
    assert_eq!(normalize(asm), expected);

    // Boot it in QEMU (requires the toolchain + QEMU). Hart 0 writes the message
    // ("H\0") to the UART, so success is "ran with no CPU fault and the UART
    // received 'H'".
    let serial = unsafe { run_program("uart_hello", ast, &configuration, &accessed) };
    assert!(
        serial.contains('H'),
        "uart_hello should write 'H' to the UART; got {serial:?}"
    );
}
