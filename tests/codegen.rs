mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

/// The UART MMIO section used by `three` (the QEMU `virt` 16550 at 0x10000000).
fn uart_section() -> Vec<Section> {
    vec![Section {
        address: MemoryValueI64::from(0x10000000),
        size: MemoryValueI64::from(1),
        permissions: Permissions::Write,
        volatile: true,
    }]
}

/// Verifies + optimizes each example program, lowers it to runnable RISC-V via
/// [`emit_executable`], and writes the result to `target/gen/<name>.s`.
///
/// This is what makes the project's output executable: the verifier infers the
/// memory layout (`value` is a global `u32`, `welcome` a thread-local `[u8 u8]`,
/// …) and `emit_executable` materializes it as `.data`/`.bss` sections plus the
/// lowered instructions, so the RISC-V GNU toolchain can assemble + link it into
/// an ELF that boots in `qemu-system-riscv64`. The generated files are assembled
/// and run by `scripts/build-run.sh`.
#[test]
fn emit_runnable_assembly() {
    let dir = env!("CARGO_MANIFEST_DIR");
    let out_dir = format!("{dir}/target/gen");
    std::fs::create_dir_all(&out_dir).unwrap();

    let programs: &[(&str, Vec<Section>)] = &[
        ("four", Vec::new()),
        ("five", Vec::new()),
        ("six", Vec::new()),
        ("three", uart_section()),
    ];

    for (name, sections) in programs {
        let (ast, configuration) =
            unsafe { verify_and_optimize(name, sections.clone(), &[1, 2]) };
        let asm = emit_executable(ast, &configuration);

        // Sanity: the emitted program must be self-contained — an entry, the
        // generated storage for every inferred variable, and a halt loop.
        assert!(asm.contains(".global _start"), "{name}: missing entry");
        assert!(asm.contains("__halt:"), "{name}: missing halt loop");
        assert!(asm.contains(".section .bss"), "{name}: missing .bss");
        for label in configuration.0.keys() {
            assert!(
                asm.contains(&format!("{label}:")),
                "{name}: missing storage for `{label}`\n{asm}"
            );
        }
        std::fs::write(format!("{out_dir}/{name}.s"), &asm).unwrap();
    }
}
