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
    emit_with_target(
        Target::BareMetal,
        ast,
        configuration,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    )
}

/// The execution target codegen lowers for.
///
/// Both run the *same verified body* on N harts; only the entry/exit plumbing
/// differs. **Bare-metal**: the machine boots the body on every hart (`-smp N`),
/// each hart derives its thread-local base from `mhartid`, and a finished hart
/// parks in a `wfi` halt loop. **Hosted Linux**: one process whose `_start`
/// spawns a thread per *extra* hart with `clone` (per-thread `tp` via
/// `CLONE_SETTLS`), so the harts run as real OS threads under user-mode
/// `qemu-riscv64` (genuine parallelism, not `-smp` round-robin); a finished hart
/// ends with the `exit` thread syscall. A single-hart program is identical under
/// both apart from that halt.
#[derive(Clone, Copy, PartialEq, Eq)]
pub enum Target {
    BareMetal,
    HostedLinux,
}

/// Like [`emit_executable`] but for the **hosted-Linux** target (user-mode
/// `qemu-riscv64`): a multi-hart program spawns one OS thread per extra hart, so
/// it gets real parallelism. See [`Target`].
pub fn emit_executable_hosted(
    ast: Option<NonNull<AstNode>>,
    configuration: &TypeConfiguration,
    accessed: &AccessedRanges,
    transitions: &AccessTransitions,
    uncompactable: &BTreeSet<Label>,
    pinned_nodes: &BTreeSet<NonNull<AstNode>>,
) -> String {
    emit_with_target(
        Target::HostedLinux,
        ast,
        configuration,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    )
}

/// Bytes of stack reserved (in `.bss`) for each spawned worker thread on the
/// hosted target. The verified programs are register-heavy with shallow call
/// depth, so this is generous.
const HOSTED_WORKER_STACK: u64 = 256 * 1024;

#[allow(clippy::too_many_arguments)]
fn emit_with_target(
    target: Target,
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

    // Per-hart thread-local storage. The verifier already models each `thread`
    // variable as a distinct copy per (contiguous) hart index; the codegen must
    // reproduce that at runtime. We lay every `thread` variable out as one block
    // and replicate it once per hart, so hart `h`'s copy of a variable is at
    // `label + h*block_size`. A hart computes its base offset `tp = mhartid *
    // block_size` once at boot (mhartid is the contiguous hart index on the
    // platforms we target), and each `la` of a thread-local adds `tp`. This is a
    // no-op for single-hart use (one copy, `tp = 0`), so it only activates when a
    // `thread` variable is actually touched by more than one hart -- leaving every
    // existing single-hart / leader-worker program byte-identical.
    let hart_copies = configuration
        .0
        .values()
        .filter_map(|(loc, _)| match loc {
            LabelLocality::Thread(harts) => harts.iter().max().map(|h| *h as usize + 1),
            LabelLocality::Global => None,
        })
        .max()
        .unwrap_or(0);
    // Offset of each thread-local within the per-hart block, and the block size
    // (8-aligned so replicas stay aligned).
    let mut tls_offset: std::collections::BTreeMap<Label, u64> = Default::default();
    let mut tls_block = 0u64;
    if hart_copies > 1 {
        for (label, (loc, ty)) in &configuration.0 {
            if !matches!(loc, LabelLocality::Thread(_)) {
                continue;
            }
            let stored = match layouts.get(label) {
                Some(layout) if layout.compact => layout.total_emitted(),
                _ => size(ty),
            };
            tls_block = tls_block.next_multiple_of(8);
            tls_offset.insert(label.clone(), tls_block);
            tls_block += stored;
        }
        tls_block = tls_block.next_multiple_of(8);
    }
    // Enable per-hart TLS only when a `thread` variable with real storage is used
    // by more than one hart (a descriptor-only read leaves the block empty, and
    // single-hart use needs no offset -- both keep the old single-copy layout).
    let tls = hart_copies > 1 && tls_block > 0;

    // The input has no explicit entry (verification starts from the first line),
    // so add the `_start` entry the linker needs. Execution begins at the first
    // instruction, exactly where verification began.
    let mut text = String::from(".global _start\n_start:\n");
    if tls {
        match target {
            // Per-hart thread-local base: tp = mhartid * block_size. `t0` is a
            // scratch here; the verified program writes every register before
            // reading it.
            Target::BareMetal => text.push_str(&format!(
                "    csrr tp, mhartid  # per-hart thread-local base\n    \
                 li t0, {tls_block}\n    mul tp, tp, t0\n"
            )),
            // Hart 0 is this thread (tp = 0); spawn one OS thread per *extra* hart
            // with `clone`, giving each its own stack and `tp = h*block_size` (via
            // CLONE_SETTLS). The child resumes after the `ecall` and jumps straight
            // to the body; the parent spawns the rest, then falls into the body
            // too. Flags are the glibc thread set (VM|FS|FILES|SIGHAND|THREAD|
            // SYSVSEM|SETTLS|PARENT_SETTID|CHILD_CLEARTID) -- the combination
            // user-mode qemu accepts. Registers are scratch (the verified program
            // writes every register before reading it).
            Target::HostedLinux => {
                text.push_str("    li tp, 0  # hart 0 thread-local base\n");
                for h in 1..hart_copies {
                    let off = h as u64 * tls_block;
                    text.push_str(&format!(
                        "    la a1, __hart{h}_stack_top\n    \
                         li a0, 0x7d0f00  # clone flags (glibc thread set)\n    \
                         la a2, __hart{h}_ptid\n    \
                         li a3, {off}  # child tp = {h}*block\n    \
                         la a4, __hart{h}_ctid\n    \
                         li a7, 220\n    ecall  # clone\n    \
                         beqz a0, __hart_body  # child -> run the body\n"
                    ));
                }
                text.push_str("__hart_body:\n");
            }
        }
    }

    // .text: walk the AST, lowering the verification directives to real RISC-V
    // and re-pointing immediates at the compacted layout where required.
    let mut next = ast;
    // An `assume:` block (`#(` ... `#)`) is verified (it narrowed the symbolic
    // state) but must not run, so it is skipped here along with its markers.
    let mut in_assume = false;
    while let Some(node) = next {
        let instr = unsafe { &node.as_ref().value.this };
        if let Instruction::Assume(assume) = instr {
            in_assume = assume.open;
            next = unsafe { node.as_ref().next };
            continue;
        }
        if in_assume {
            next = unsafe { node.as_ref().next };
            continue;
        }
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
            // `forget` is a verifier-only havoc; it emits nothing.
            Instruction::Forget(_) => {}
            // `fail` must be proven unreachable; trap if somehow reached.
            Instruction::Fail(_) => text.push_str("    ebreak  # fail (proven unreachable)\n"),
            // `unreachable` / program end: halt.
            Instruction::Unreachable(_) => {
                text.push_str("    j __halt  # unreachable (program end)\n")
            }
            // Address of a per-hart thread-local: add the hart's TLS base (`tp`).
            Instruction::La(La { register, label })
                if tls && matches!(configuration.get(label), Some((Locality::Thread, _))) =>
            {
                text.push_str(&format!(
                    "    la {register}, {label}\n    add {register}, {register}, tp  # thread-local\n"
                ));
            }
            // Labels and `.global` print at column 0; everything else is indented.
            Instruction::Label(_) | Instruction::Global(_) => text.push_str(&format!("{instr}\n")),
            other => text.push_str(&format!("    {other}\n")),
        }
        next = unsafe { node.as_ref().next };
    }
    // Program end. Bare metal parks in a `wfi` loop so execution never runs off
    // the end of `.text`; hosted ends the hart's thread with the `exit` syscall,
    // so once every hart's thread has exited the process ends -- with whatever the
    // finishing hart printed already on stdout.
    match target {
        Target::BareMetal => text.push_str("__halt:\n    wfi\n    j __halt\n"),
        Target::HostedLinux => {
            text.push_str("__halt:\n    li a0, 0\n    li a7, 93\n    ecall  # exit (this thread)\n")
        }
    }

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
    for (label, (loc, ty)) in &configuration.0 {
        // Thread-locals are emitted together as the per-hart block below.
        if tls && matches!(loc, LabelLocality::Thread(_)) {
            continue;
        }
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
    // The per-hart thread-local block: block 0 carries the labels at their computed
    // offsets; `hart_copies - 1` further block_size copies reserve the other harts'.
    if tls {
        bss.push_str("    .balign 8\n");
        let mut emitted = 0u64;
        for (label, (loc, ty)) in &configuration.0 {
            if !matches!(loc, LabelLocality::Thread(_)) {
                continue;
            }
            let off = tls_offset[label];
            if off > emitted {
                bss.push_str(&format!("    .zero {}\n", off - emitted));
                emitted = off;
            }
            let stored = match layouts.get(label) {
                Some(layout) if layout.compact => layout.total_emitted(),
                _ => size(ty),
            };
            bss.push_str(&format!("{label}:\n"));
            if stored > 0 {
                bss.push_str(&format!("    .zero {stored}\n"));
                emitted += stored;
            }
        }
        if tls_block > emitted {
            bss.push_str(&format!("    .zero {}\n", tls_block - emitted));
        }
        if hart_copies > 1 {
            bss.push_str(&format!(
                "    .zero {}  # {} more per-hart copies\n",
                (hart_copies as u64 - 1) * tls_block,
                hart_copies - 1
            ));
        }
    }
    // Per-worker stacks + clone tid slots for the hosted target's spawned harts
    // (zero-init `.bss`, so they cost nothing in the ELF). The stack top label is
    // the high end, since the stack grows down.
    if target == Target::HostedLinux && tls {
        for h in 1..hart_copies {
            bss.push_str(&format!(
                "    .balign 8\n__hart{h}_ptid:\n    .zero 4\n__hart{h}_ctid:\n    .zero 4\n    \
                 .balign 16\n    .zero {HOSTED_WORKER_STACK}\n__hart{h}_stack_top:\n"
            ));
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
            | Instruction::Lh(_)
            | Instruction::Sw(_)
            | Instruction::Sb(_)
            | Instruction::Sh(_)
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
        Instruction::Lh(lh) => lh.offset = Offset { value },
        Instruction::Sw(sw) => sw.offset = Offset { value },
        Instruction::Sb(sb) => sb.offset = Offset { value },
        Instruction::Sh(sh) => sh.offset = Offset { value },
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
