//! Lowers a verified + optimized program into runnable RISC-V assembly.
//!
//! The input dialect leaves the memory layout *implicit*: variables are declared
//! with `#$`/`#&` annotations and the verifier *infers* their types and locality
//! (the [`TypeConfiguration`]). This module turns that inferred layout into a
//! concrete, assembler-ready program: the optimized instructions (with the
//! verification directives lowered to real instructions or comments) followed by
//! generated `.data`/`.bss` sections. The result assembles with the RISC-V GNU
//! toolchain (`as` + `ld`) and boots under `qemu-system-riscv64 -machine virt`.

use crate::verifier_types::*;
use crate::*;
use std::collections::BTreeSet;
use std::ptr::NonNull;

/// Emits a complete, runnable RISC-V program for the verified + optimized `ast`
/// and the memory layout the verifier inferred (`configuration`).
///
/// Directive lowering:
/// - `#$ …` (define) — metadata only, kept as a comment.
/// - `#& reg, label` (lat) — lowered to `la reg, __<label>_type`, loading the
///   address of the generated runtime type descriptor.
/// - `#!` (fail) — should be proven unreachable; lowered to `ebreak` as a guard.
/// - `#?` (unreachable / program end) — lowered to a jump to the halt loop.
///
/// A `__halt: wfi; j __halt` loop is appended so execution never runs off the end
/// of `.text`. Then `.data` holds the runtime type descriptors read via `#&`, and
/// `.bss` holds zero-initialized storage for every inferred variable.
pub fn emit_executable(ast: Option<NonNull<AstNode>>, configuration: &TypeConfiguration) -> String {
    // Labels whose runtime *type descriptor* is read (via `#&` / lat).
    let mut lat_labels: BTreeSet<Label> = BTreeSet::new();
    let mut next = ast;
    while let Some(node) = next {
        let value = unsafe { &node.as_ref().value };
        if let Instruction::Lat(Lat { label, .. }) = &value.this {
            lat_labels.insert(label.clone());
        }
        next = unsafe { node.as_ref().next };
    }

    // The input has no explicit entry (verification starts from the first line),
    // so add the `_start` entry the linker needs. Execution begins at the first
    // instruction, exactly where verification began.
    let mut text = String::from(".global _start\n_start:\n");

    // .text — walk the AST, lowering the verification directives to real RISC-V.
    let mut next = ast;
    while let Some(node) = next {
        let instr = unsafe { &node.as_ref().value.this };
        match instr {
            // Type annotation — metadata only; keep as a comment (`#` starts a
            // RISC-V comment, so its `Display` is already comment-safe).
            Instruction::Define(_) => text.push_str(&format!("    {instr}\n")),
            // Load-address-of-type — load the generated descriptor's address.
            Instruction::Lat(Lat { register, label }) => text.push_str(&format!(
                "    la {register}, __{label}_type  # #& {register}, {label}\n"
            )),
            // `fail` must be proven unreachable; trap if somehow reached.
            Instruction::Fail(_) => text.push_str("    ebreak  # fail (proven unreachable)\n"),
            // `unreachable` / program end — halt.
            Instruction::Unreachable(_) => {
                text.push_str("    j __halt  # unreachable (program end)\n")
            }
            // Labels and `.global` print at column 0; everything else is indented.
            Instruction::Label(_) | Instruction::Global(_) => text.push_str(&format!("{instr}\n")),
            other => text.push_str(&format!("    {other}\n")),
        }
        next = unsafe { node.as_ref().next };
    }
    // Halt loop, so execution never runs off the end of `.text`.
    text.push_str("__halt:\n    wfi\n    j __halt\n");

    // .data — initialized runtime type descriptors, read by the lowered `#&`.
    let mut data = String::new();
    for label in &lat_labels {
        if let Some((_locality, ty)) = configuration.get(label) {
            emit_type_descriptor(&mut data, &format!("__{label}"), ty);
        }
    }

    // .bss — zero-initialized storage for every inferred variable.
    let mut bss = String::new();
    for (label, (_locality, ty)) in &configuration.0 {
        // `.balign 8` keeps word/doubleword accesses aligned.
        bss.push_str(&format!("    .balign 8\n{label}:\n    .zero {}\n", size(ty)));
    }

    let mut out = text;
    if !data.is_empty() {
        out.push_str("\n.section .data\n");
        out.push_str(&data);
    }
    if !bss.is_empty() {
        out.push_str("\n.section .bss\n");
        out.push_str(&bss);
    }
    out
}

/// Emits the runtime type descriptor for `ty` under the symbol `<name>_type`.
///
/// The on-target layout matches what the verifier builds in `MemoryMap::set_type`
/// and what the asset programs read: a 25-byte record
/// `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]`, with `List`
/// types followed by a `<name>_subtypes` array of one such record per element.
/// (Records are deliberately *not* padded — the programs stride them by 25 bytes.)
fn emit_type_descriptor(out: &mut String, name: &str, ty: &Type) {
    match ty {
        Type::List(subtypes) => {
            let flat = FlatType::from(ty) as u64;
            out.push_str(&format!("{name}_type:\n"));
            out.push_str(&format!("    .dword {flat}                # List\n"));
            out.push_str(&format!("    .dword {name}_subtypes      # subtypes\n"));
            out.push_str(&format!("    .dword {}                # length\n", subtypes.len()));
            out.push_str("    .byte 1                    # locality\n");
            out.push_str(&format!("{name}_subtypes:\n"));
            for sub in subtypes {
                emit_descriptor_record(out, sub);
            }
        }
        _ => {
            out.push_str(&format!("{name}_type:\n"));
            emit_descriptor_record(out, ty);
        }
    }
}

/// Emits one inline 25-byte descriptor record (no symbol). Only the scalar and
/// single-level-`List` cases the asset programs use are modelled here; a nested
/// `List`/`Union` subtype would need its own `_subtypes` symbol.
fn emit_descriptor_record(out: &mut String, ty: &Type) {
    let flat = FlatType::from(ty) as u64;
    let length = match ty {
        Type::List(subtypes) => subtypes.len(),
        _ => 0,
    };
    out.push_str(&format!("    .dword {flat}\n"));
    out.push_str("    .dword 0\n");
    out.push_str(&format!("    .dword {length}\n"));
    out.push_str("    .byte 1\n");
}
