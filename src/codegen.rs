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

/// Emits a complete, runnable RISC-V program for the verified + optimized `ast`,
/// the memory layout the verifier inferred (`configuration`), and the byte ranges
/// the program was proven to access at runtime (`accessed`).
///
/// Directive lowering:
/// - `#$ …` (define) — metadata only, kept as a comment.
/// - `#@ …` (region) — metadata only (verified at compile time), kept as a comment.
/// - `#& reg, label` (lat) — lowered to `la reg, __<label>_type`, loading the
///   address of the generated runtime type descriptor.
/// - `#!` (fail) — should be proven unreachable; lowered to `ebreak` as a guard.
/// - `#?` (unreachable / program end) — lowered to a jump to the halt loop.
///
/// A `__halt: wfi; j __halt` loop is appended so execution never runs off the end
/// of `.text`. Then `.data` holds the runtime type descriptors read via `#&`, and
/// `.bss` holds zero-initialized storage for every inferred variable.
///
/// **Dead-data elimination.** Information only read at *compile time* need not
/// exist in the output program. The verifier records (in `accessed`) every byte
/// the program can load or store at runtime across all proven paths; descriptor
/// bytes outside those ranges — e.g. each record's locality byte, which these
/// programs only consult through the verifier — are emitted as zero padding when
/// a later record's (strided) offset depends on them, and not emitted at all when
/// trailing.
pub fn emit_executable(
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    accessed: &AccessedRanges,
) -> String {
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
            emit_type_descriptor(&mut data, &format!("__{label}"), ty, accessed);
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

/// The runtime-accessed byte ranges of one emitted region (e.g. `__welcome_type`
/// or `__welcome_subtypes`), used to decide which descriptor bytes must exist in
/// the output. A byte no range covers is only ever read at *compile time* (by the
/// verifier) so its value is dead: it survives as zero padding when a live byte
/// follows it (the programs stride descriptor records by their full 25 bytes), and
/// is not emitted at all when trailing.
struct Coverage<'a>(Option<&'a BTreeSet<(u64, u64)>>);

impl Coverage<'_> {
    /// Whether any runtime access touches a byte in `[lo, hi)`.
    fn hit(&self, lo: u64, hi: u64) -> bool {
        self.0
            .is_some_and(|ranges| ranges.iter().any(|&(start, end)| start < hi && end > lo))
    }
    /// One past the last runtime-accessed byte of the region.
    fn live_end(&self) -> u64 {
        self.0
            .and_then(|ranges| ranges.iter().map(|&(_, end)| end).max())
            .unwrap_or(0)
    }
}

/// Emits the runtime type descriptor for `ty` under the symbol `<name>_type`.
///
/// The on-target layout matches what the verifier builds in `MemoryMap::set_type`
/// and what the asset programs read: a 25-byte record
/// `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]`, with `List`
/// types followed by a `<name>_subtypes` array of one such record per element.
/// (Records are deliberately *not* padded — the programs stride them by 25 bytes.)
/// Only the bytes in `accessed` (what the program can read at runtime) are emitted
/// with their values — see [`emit_executable`]'s dead-data-elimination note.
fn emit_type_descriptor(out: &mut String, name: &str, ty: &Type, accessed: &AccessedRanges) {
    let top = Coverage(accessed.get(&Label {
        tag: format!("{name}_type"),
    }));
    out.push_str(&format!("{name}_type:\n"));
    match ty {
        Type::List(subtypes) => {
            let flat = FlatType::from(ty) as u64;
            emit_descriptor_record(
                out,
                &top,
                0,
                [
                    format!(".dword {flat}                # List"),
                    format!(".dword {name}_subtypes      # subtypes"),
                    format!(".dword {}                # length", subtypes.len()),
                    String::from(".byte 1                    # locality"),
                ],
            );
            let sub = Coverage(accessed.get(&Label {
                tag: format!("{name}_subtypes"),
            }));
            out.push_str(&format!("{name}_subtypes:\n"));
            for (index, subtype) in subtypes.iter().enumerate() {
                emit_descriptor_record(out, &sub, 25 * index as u64, leaf_record_fields(subtype));
            }
        }
        _ => {
            emit_descriptor_record(out, &top, 0, leaf_record_fields(ty));
        }
    }
}

/// The four field directives of one inline 25-byte descriptor record. Only the
/// scalar and single-level-`List` cases the asset programs use are modelled here;
/// a nested `List`/`Union` subtype would need its own `_subtypes` symbol.
fn leaf_record_fields(ty: &Type) -> [String; 4] {
    let flat = FlatType::from(ty) as u64;
    let length = match ty {
        Type::List(subtypes) => subtypes.len(),
        _ => 0,
    };
    [
        format!(".dword {flat}"),
        String::from(".dword 0"),
        format!(".dword {length}"),
        String::from(".byte 1"),
    ]
}

/// Emits one 25-byte descriptor record starting at byte `base` of its region,
/// keeping only the bytes the program accesses at runtime: a live field is emitted
/// with its value; a dead field a later live byte depends on (the records are
/// strided by 25 bytes) becomes `.zero` padding; trailing dead bytes are omitted.
fn emit_descriptor_record(out: &mut String, coverage: &Coverage, base: u64, fields: [String; 4]) {
    // The record's fields sit at relative offsets 0, 8, 16, 24 (sizes 8, 8, 8, 1).
    const FIELD_SIZES: [u64; 4] = [8, 8, 8, 1];
    let live_end = coverage.live_end();
    let mut offset = base;
    let mut padding = 0;
    for (size, directive) in FIELD_SIZES.into_iter().zip(fields) {
        if coverage.hit(offset, offset + size) {
            if padding > 0 {
                out.push_str(&format!(
                    "    .zero {padding}                # never accessed at runtime (padding)\n"
                ));
                padding = 0;
            }
            out.push_str(&format!("    {directive}\n"));
        } else {
            padding += size;
        }
        offset += size;
    }
    // Dead bytes before a later live byte keep the strided offsets intact; dead
    // bytes after the region's last live byte are dropped entirely.
    if padding > 0 && live_end > offset {
        out.push_str(&format!(
            "    .zero {padding}                # never accessed at runtime (padding)\n"
        ));
    }
}
