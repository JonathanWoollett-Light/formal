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
use std::collections::{BTreeMap, BTreeSet};
use std::ptr::NonNull;

/// Emits a complete, runnable RISC-V program for the verified + optimized `ast`,
/// the memory layout the verifier inferred (`configuration`), and the proof's
/// runtime-access records (`accessed`/`transitions`/`uncompactable`).
///
/// Directive lowering:
/// - `#$ …` (define): metadata only, kept as a comment.
/// - `#@ …` (region): metadata only (verified at compile time), kept as a comment.
/// - `#& reg, label` (lat): lowered to `la reg, __<label>_type`, loading the
///   address of the generated runtime type descriptor.
/// - `#!` (fail): should be proven unreachable; lowered to `ebreak` as a guard.
/// - `#?` (unreachable / program end): lowered to a jump to the halt loop.
///
/// A `__halt: wfi; j __halt` loop is appended so execution never runs off the end
/// of `.text`. Then `.data` holds the runtime type descriptors read via `#&`, and
/// `.bss` holds zero-initialized storage for every inferred variable.
///
/// **Dead-data elimination & layout compaction.** Information only read at
/// *compile time* need not exist in the output program. The verifier records (in
/// `accessed`) every byte the program can load or store at runtime across all
/// proven paths, and (in `transitions`) which instruction computes which offset.
/// Bytes outside the accessed ranges are **removed** from the emitted layout, and
/// every instruction whose address arithmetic spans a removed gap has its
/// immediate rewritten to the compacted offset (`f(to) - f(from)`): e.g. a loop
/// striding 25-byte descriptor records whose middle 17 bytes are never read is
/// rewritten to stride 8. A single immediate must satisfy *every* recorded
/// execution of its instruction; where it cannot (or where the verifier marked
/// the region `uncompactable` because an offset was only known as a range), the
/// region falls back to the padded layout: dead bytes below the region's last
/// live byte survive as `.zero` padding and only trailing dead bytes are
/// dropped. Compaction can relocate accesses to different alignments; QEMU
/// `virt` emulates misaligned access (the 25-byte records already rely on it),
/// but stricter hardware may require an alignment-preserving layout (a future
/// refinement).
pub fn emit_executable(
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned_nodes: &BTreeSet<NonNull<AstNode>>,
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

    // The (compacted or padded) layout of every region this program emits, and
    // the per-instruction immediate rewrites compaction requires.
    let (layouts, rewrites) = solve_layouts(
        ast,
        configuration,
        &lat_labels,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    );

    // The input has no explicit entry (verification starts from the first line),
    // so add the `_start` entry the linker needs. Execution begins at the first
    // instruction, exactly where verification began.
    let mut text = String::from(".global _start\n_start:\n");

    // .text: walk the AST, lowering the verification directives to real RISC-V
    // and re-pointing immediates at the compacted layout where required.
    let mut next = ast;
    while let Some(node) = next {
        let instr = unsafe { &node.as_ref().value.this };
        let patched = rewrites
            .get(&node)
            .and_then(|immediate| patch_immediate(instr, *immediate));
        let instr = patched.as_ref().unwrap_or(instr);
        match instr {
            // Type annotation: metadata only; keep as a comment (`#` starts a
            // RISC-V comment, so its `Display` is already comment-safe).
            Instruction::Define(_) => text.push_str(&format!("    {instr}\n")),
            // Load-address-of-type: load the generated descriptor's address.
            Instruction::Lat(Lat { register, label }) => text.push_str(&format!(
                "    la {register}, __{label}_type  # #& {register}, {label}\n"
            )),
            // `fail` must be proven unreachable; trap if somehow reached.
            Instruction::Fail(_) => text.push_str("    ebreak  # fail (proven unreachable)\n"),
            // `unreachable` / program end: halt.
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

    // .data: initialized runtime type descriptors, read by the lowered `#&`.
    let mut data = String::new();
    for label in &lat_labels {
        if let Some((_locality, ty)) = configuration.get(label) {
            emit_type_descriptor(&mut data, &format!("__{label}"), ty, &layouts);
        }
    }

    // .bss: zero-initialized storage for every inferred variable, compacted to
    // its runtime-accessed bytes where the layout allows.
    let mut bss = String::new();
    for (label, (_locality, ty)) in &configuration.0 {
        let stored = match layouts.get(label) {
            Some(layout) if layout.compact => layout.total_emitted(),
            _ => size(ty),
        };
        // `.balign 8` keeps word/doubleword accesses aligned.
        bss.push_str(&format!("    .balign 8\n{label}:\n"));
        if stored > 0 {
            bss.push_str(&format!("    .zero {stored}\n"));
        }
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

/// The layout of one emitted region: which old-offset byte ranges are emitted,
/// and whether the gaps between them are removed (`compact`) or kept as `.zero`
/// padding.
struct Layout {
    /// Emitted old-offset ranges, ascending and disjoint.
    emitted: Vec<(u64, u64)>,
    /// One past the last byte of the region under the *old* layout (its size).
    size: u64,
    /// Whether gaps are removed (offsets re-pointed via [`Layout::f`]) or kept
    /// as padding (identity offsets).
    compact: bool,
}

impl Layout {
    /// Maps an old offset to its emitted offset. Identity for padded layouts.
    /// For compacted layouts: inside an emitted range, its position among the
    /// emitted bytes; inside a gap, the position the next emitted byte takes
    /// (gap bytes are never dereferenced; that is what made them gaps); past
    /// the region's end, the emitted total plus the overhang, so a pointer that
    /// strides one whole record past the end (a loop's final, never-dereferenced
    /// step) keeps a consistent stride.
    fn f(&self, offset: u64) -> u64 {
        if !self.compact {
            return offset;
        }
        let mut emitted_below = 0;
        for &(start, end) in &self.emitted {
            if offset < start {
                return emitted_below;
            }
            if offset < end {
                return emitted_below + (offset - start);
            }
            emitted_below += end - start;
        }
        emitted_below + offset.saturating_sub(self.size)
    }

    fn total_emitted(&self) -> u64 {
        self.emitted.iter().map(|(start, end)| end - start).sum()
    }

    /// One past the last emitted (old-offset) byte; the padded layout drops
    /// everything after it.
    fn live_end(&self) -> u64 {
        self.emitted.last().map(|&(_, end)| end).unwrap_or(0)
    }

    /// Whether the (field) starting at `offset` is emitted.
    fn emits(&self, offset: u64) -> bool {
        self.emitted
            .iter()
            .any(|&(start, end)| offset >= start && offset < end)
    }
}

/// Builds the layout of every region the program emits and (under those
/// layouts) the immediate each recorded instruction must carry. A node whose
/// recorded executions cannot agree on a single immediate forces its regions
/// back to the padded (identity) layout; the fixpoint iterates in AST order so
/// any cascade is deterministic.
#[allow(clippy::too_many_arguments)]
fn solve_layouts(
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    lat_labels: &BTreeSet<Label>,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned_nodes: &BTreeSet<NonNull<AstNode>>,
) -> (BTreeMap<Label, Layout>, BTreeMap<NonNull<AstNode>, i64>) {
    let mut layouts = BTreeMap::new();
    // Descriptor regions (field-granular).
    for label in lat_labels {
        if let Some((_locality, ty)) = configuration.get(label) {
            let top = Label {
                tag: format!("__{label}_type"),
            };
            layouts.insert(top.clone(), descriptor_layout(accessed.get(&top), 1));
            if let Type::List(subtypes) = ty {
                let sub = Label {
                    tag: format!("__{label}_subtypes"),
                };
                layouts.insert(
                    sub.clone(),
                    descriptor_layout(accessed.get(&sub), subtypes.len() as u64),
                );
            }
        }
    }
    // Variable storage regions (byte-granular).
    for (label, (_locality, ty)) in &configuration.0 {
        layouts.insert(
            label.clone(),
            variable_layout(accessed.get(label), size(ty)),
        );
    }
    // Compact unless the verifier saw an under-determined offset into the region.
    for (label, layout) in layouts.iter_mut() {
        layout.compact = !uncompactable.contains(label);
    }

    // Nodes in deterministic program order.
    let mut nodes = Vec::new();
    let mut next = ast;
    while let Some(node) = next {
        nodes.push(node);
        next = unsafe { node.as_ref().next };
    }

    // Fixpoint: demote regions until every recorded node can carry one
    // immediate. A node fails when its records disagree, when it is *pinned*
    // (it also executed with a raw address / scalar operand / range offset,
    // executions invisible to `transitions`) yet compaction would change its
    // immediate, or when the required change cannot be patched into its
    // instruction at all.
    loop {
        let mut changed = false;
        for node in &nodes {
            let Some(records) = transitions.get(node) else {
                continue;
            };
            let satisfiable = match required_immediate(records, &layouts) {
                None => false,
                Some(required) => {
                    let unchanged = records.iter().next().is_some_and(|(_, from, to)| {
                        required as i128 == *to as i128 - *from as i128
                    });
                    unchanged || (!pinned_nodes.contains(node) && patchable(*node))
                }
            };
            if !satisfiable {
                for (label, _, _) in records {
                    if let Some(layout) = layouts.get_mut(label) {
                        if layout.compact {
                            layout.compact = false;
                            changed = true;
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Collect the rewrites the settled layouts require.
    let mut rewrites = BTreeMap::new();
    for node in &nodes {
        let Some(records) = transitions.get(node) else {
            continue;
        };
        let Some(required) = required_immediate(records, &layouts) else {
            continue;
        };
        // The original immediate is `to - from` of any record (an invariant of
        // how transitions are recorded); rewrite only when compaction moved it,
        // which the fixpoint only permits for unpinned, patchable nodes.
        let original = records
            .iter()
            .next()
            .map(|(_, from, to)| *to as i128 - *from as i128);
        if Some(required as i128) != original {
            debug_assert!(!pinned_nodes.contains(node) && patchable(*node));
            rewrites.insert(*node, required);
        }
    }

    (layouts, rewrites)
}

/// The single immediate satisfying every recorded execution of one node under
/// the given layouts (`f(to) - f(from)` must agree across records), or `None`
/// when no single immediate can.
fn required_immediate(
    records: &BTreeSet<(Label, u64, u64)>,
    layouts: &BTreeMap<Label, Layout>,
) -> Option<i64> {
    let mut required: Option<i128> = None;
    for (label, from, to) in records {
        let delta = match layouts.get(label) {
            Some(layout) => layout.f(*to) as i128 - layout.f(*from) as i128,
            // A region this program does not emit keeps its old offsets.
            None => *to as i128 - *from as i128,
        };
        match required {
            None => required = Some(delta),
            Some(existing) if existing == delta => {}
            Some(_) => return None,
        }
    }
    required.and_then(|value| i64::try_from(value).ok())
}

/// Field-granular layout of a descriptor region: `record_count` 25-byte records
/// of fields `[u64, u64, u64, u8]`. A field is emitted iff any accessed range
/// touches it: values can only be emitted whole-field (a `.dword` holding a
/// relocation cannot be split), which also over-covers partially-accessed fields
/// (the sound direction).
fn descriptor_layout(ranges: Option<&BTreeSet<(u64, u64)>>, record_count: u64) -> Layout {
    const FIELD_SIZES: [u64; 4] = [8, 8, 8, 1];
    let mut emitted = Vec::new();
    for record in 0..record_count {
        let mut offset = record * 25;
        for field in FIELD_SIZES {
            let live = ranges.is_some_and(|rs| {
                rs.iter()
                    .any(|&(start, end)| start < offset + field && end > offset)
            });
            if live {
                emitted.push((offset, offset + field));
            }
            offset += field;
        }
    }
    Layout {
        emitted,
        size: record_count * 25,
        compact: false,
    }
}

/// Byte-granular layout of a variable's storage: the accessed ranges, clamped
/// to the region and merged into disjoint ascending runs.
fn variable_layout(ranges: Option<&BTreeSet<(u64, u64)>>, size: u64) -> Layout {
    let mut emitted: Vec<(u64, u64)> = Vec::new();
    if let Some(ranges) = ranges {
        for &(start, end) in ranges {
            let (start, end) = (start.min(size), end.min(size));
            if start >= end {
                continue;
            }
            match emitted.last_mut() {
                Some(last) if start <= last.1 => last.1 = last.1.max(end),
                _ => emitted.push((start, end)),
            }
        }
    }
    Layout {
        emitted,
        size,
        compact: false,
    }
}

/// Whether [`patch_immediate`] can rewrite this node's instruction; anything
/// else with recorded transitions must keep its original immediate (the
/// fixpoint demotes its regions instead).
fn patchable(node: NonNull<AstNode>) -> bool {
    matches!(
        unsafe { &node.as_ref().value.this },
        Instruction::Addi(_)
            | Instruction::Ld(_)
            | Instruction::Lw(_)
            | Instruction::Lb(_)
            | Instruction::Sw(_)
            | Instruction::Sb(_)
    )
}

/// Re-points an instruction's offset/immediate at the compacted layout. Returns
/// `None` for instructions without a rewritable immediate (the fixpoint only
/// lets rewrites reach [`patchable`] nodes, so this is defensive).
fn patch_immediate(instruction: &Instruction, immediate: i64) -> Option<Instruction> {
    let value = Immediate {
        radix: 10,
        value: immediate,
    };
    let mut patched = instruction.clone();
    match &mut patched {
        Instruction::Addi(addi) => addi.rhs = value,
        Instruction::Ld(ld) => ld.offset = Offset { value },
        Instruction::Lw(lw) => lw.offset = Offset { value },
        Instruction::Lb(lb) => lb.offset = Offset { value },
        Instruction::Sw(sw) => sw.offset = Offset { value },
        Instruction::Sb(sb) => sb.offset = Offset { value },
        _ => return None,
    }
    Some(patched)
}

/// Emits the runtime type descriptor for `ty` under the symbol `<name>_type`.
///
/// The on-target layout matches what the verifier builds in `MemoryMap::set_type`
/// and what the asset programs read: a 25-byte record
/// `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]`, with `List`
/// types followed by a `<name>_subtypes` array of one such record per element,
/// **minus** whatever the region's [`Layout`] removed or padded (see
/// [`emit_executable`]'s dead-data note).
fn emit_type_descriptor(
    out: &mut String,
    name: &str,
    ty: &Type,
    layouts: &BTreeMap<Label, Layout>,
) {
    static EMPTY: Layout = Layout {
        emitted: Vec::new(),
        size: 0,
        compact: true,
    };
    let top = layouts
        .get(&Label {
            tag: format!("{name}_type"),
        })
        .unwrap_or(&EMPTY);
    out.push_str(&format!("{name}_type:\n"));
    match ty {
        Type::List(subtypes) => {
            let flat = FlatType::from(ty) as u64;
            emit_descriptor_record(
                out,
                top,
                0,
                [
                    format!(".dword {flat}                # List"),
                    format!(".dword {name}_subtypes      # subtypes"),
                    format!(".dword {}                # length", subtypes.len()),
                    String::from(".byte 1                    # locality"),
                ],
            );
            let sub = layouts
                .get(&Label {
                    tag: format!("{name}_subtypes"),
                })
                .unwrap_or(&EMPTY);
            out.push_str(&format!("{name}_subtypes:\n"));
            for (index, subtype) in subtypes.iter().enumerate() {
                emit_descriptor_record(out, sub, 25 * index as u64, leaf_record_fields(subtype));
            }
        }
        _ => {
            emit_descriptor_record(out, top, 0, leaf_record_fields(ty));
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

/// Emits one 25-byte descriptor record starting at old-offset `base` of its
/// region: live fields with their values; dead fields *removed* under a
/// compacted layout (the accessing instructions were re-pointed), or, under a
/// padded layout, kept as `.zero` padding below the region's last live byte
/// with trailing dead bytes dropped.
fn emit_descriptor_record(out: &mut String, layout: &Layout, base: u64, fields: [String; 4]) {
    const FIELD_SIZES: [u64; 4] = [8, 8, 8, 1];
    let live_end = layout.live_end();
    let mut offset = base;
    let mut padding = 0;
    for (size, directive) in FIELD_SIZES.into_iter().zip(fields) {
        if layout.emits(offset) {
            if padding > 0 {
                out.push_str(&format!(
                    "    .zero {padding}                # never accessed at runtime (padding)\n"
                ));
                padding = 0;
            }
            out.push_str(&format!("    {directive}\n"));
        } else if !layout.compact {
            padding += size;
        }
        offset += size;
    }
    // Dead bytes before a later live byte keep the padded layout's offsets
    // intact; dead bytes after the region's last live byte are dropped.
    if padding > 0 && live_end > offset {
        out.push_str(&format!(
            "    .zero {padding}                # never accessed at runtime (padding)\n"
        ));
    }
}
