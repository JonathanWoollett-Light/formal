# CLAUDE.md

Development guidance for `formal`. For *usage* (installation, running, QEMU
workflow) see [README.md](README.md). For design intent and longer-form notes
see [language.md](language.md). This file is the cached, precise description of
how the codebase works.

---

## 1. What this is

`formal` is a compiler/formal-verifier for an annotated dialect of RISC-V
assembly aimed at bare-metal RISC-V. Its distinguishing idea: a program is only
accepted if it can be **proven** correct across *every* hart (hardware thread)
interleaving and *every* admissible type/locality assignment of its
under-specified variables. "Correct" means **no `#!` ("fail") marker is
reachable** and every memory access is in bounds / permitted. The proof
additionally *infers* each variable's type and locality and yields the
reachable-node / taken-branch sets that drive optimization.

The verifier is a symbolic interpreter over abstract (interval / tagged-pointer)
values, exploring an explicit execution tree.

### Current status (verify before relying on any of this)

- **Crate layout**: builds as a **library** (`src/lib.rs`, crate `formal`) plus
  a thin binary (`src/main.rs`). The library exposes the whole pipeline so the
  integration tests can call it.
- **Builds**: `cargo build` succeeds (two `unused import` warnings:
  `tracing::error` in [src/verifier.rs](src/verifier.rs) and
  [src/verifier_types.rs](src/verifier_types.rs)).
- **Exploration is deterministic.** The same program + system configuration
  always produces the same step sequence, configuration and output (see the
  determinism note at the end of [§4.3](#43-verification--explorerer)).
- **`cargo test` passes.** The verifier is exercised through the integration
  tests in [tests/](tests/) (`uart_hello`/`racy_increment`/`racy_store_inferred`/`racy_store_annotated`/`heap_regions`), which parse,
  verify and optimize the example programs and assert the inferred
  `TypeConfiguration`, the **runtime-accessed byte ranges** (`accessed` — drives
  dead-data elimination in codegen, [§4.8](#48-code-generation--emit_executable-srccodegenrs)),
  the optimized output, the exact emitted program, and the **exact incremental**
  behaviour of the state machine (a full per-step trace for `racy_store_inferred`/`racy_store_annotated`; the
  exact step count and type-inference timeline for `racy_increment`/`uart_hello`). `raw_access_undeclared` pins
  the every-access-must-verify rule (a raw access no `#@` region describes →
  `Invalid`). See [§6](#6-integration-tests-tests).
- **`cargo run` panics.** [src/main.rs](src/main.rs) hard-codes its input to
  [assets/two.s](assets/two.s), which uses the readable `lat`/`branch` spellings
  the parser does not accept (only `#&` and `j` are accepted), so parsing hits
  `todo!()` at [src/ast.rs:238](src/ast.rs#L238). Even with a parseable input,
  `main` ends in `todo!()` right after `print_ast` — the verifier is **not**
  wired into the binary.

So today the working surface is: *parse → compress → (verify, via the integration
tests) → optimize → print*. Treat the binary `main` as a scratch harness.

## 2. Commands

```sh
cargo build                 # compile lib + binary
cargo run                   # scratch harness (currently panics — see above)
cargo test                  # run the integration tests over the example programs
cargo test --test uart_hello     # run a single integration-test binary
cargo test --test uart_hello -- --nocapture   # with stdout passthrough
cargo fix --lib -p formal   # clears the two unused-import warnings
```

Run tests in a **debug build** (the default): the verifier's internal
`(0..N)` loop guards and the `excluded`/`counter`/`hash`/`last_out` fields are
behind `#[cfg(debug_assertions)]`.

## 3. Repository layout

| Path | Role |
|------|------|
| [src/lib.rs](src/lib.rs) | Library root: declares + re-exports the modules, and defines `compress` (node re-allocation) and `print_ast` (serialization). |
| [src/main.rs](src/main.rs) | Thin binary; `use formal::*` then parse → compress → print → `todo!()`. |
| [src/ast.rs](src/ast.rs) | Lexer/parser front-end: `AstNode` intrusive list, `Instruction` enum, all operand types, per-instruction parsers and `Display` impls. |
| [src/verifier.rs](src/verifier.rs) | The `Explorerer` state machine — the heart of verification. |
| [src/verifier_types.rs](src/verifier_types.rs) | Symbolic value & memory model, `State`, `TypeConfiguration`, runtime type reflection. No `unsafe`. |
| [src/optimizer.rs](src/optimizer.rs) | `remove_untouched` and `remove_branches` post-proof optimizations. |
| [src/codegen.rs](src/codegen.rs) | `emit_executable` — lowers the verified+optimized AST + inferred layout into runnable RISC-V (generated `.data`/`.bss` + lowered directives). |
| [src/draw.rs](src/draw.rs) | `draw_tree` — ASCII rendering of a `VerifierNode` tree (debug/diagnostic). |
| [tests/](tests/) | Integration tests (one binary per file, named after the behaviour they pin — see [§6](#6-integration-tests-tests)): `common/mod.rs` helpers + the pipeline tests (`uart_hello`, `racy_*`, `heap_regions`, …) and behaviour-focused tests (`vague_access`, `region_*`, `conflicting_defines`, …). The Valid-outcome tests also lower their output and **boot it in QEMU**. |
| [scripts/build-run.sh](scripts/build-run.sh) | Assemble + link (`as`/`ld`) the generated `target/gen/*.s` and boot in QEMU. |
| [assets/](assets/) | Example programs `*.s`; `uart_hello_ast.s` is the golden parsed/compressed form of `uart_hello.s`. |
| [language.md](language.md) | Design notes (placement, racy-ness, list/union exploration, complexity, toolchain). |

## 4. The compilation & verification pipeline (precise description)

The pipeline, as orchestrated in [src/main.rs](src/main.rs) and the tests, is:

```
new_ast (parse)  →  compress  →  Explorerer / next_step (verify)  →  remove_untouched / remove_branches (optimize)  →  print_ast (serialize) / emit_executable (codegen)
```

### 4.1 Parsing — `new_ast` ([src/ast.rs:65](src/ast.rs#L65))

Input is the whole source as a `&[char]`. There is no separate tokenizer; the
parser matches raw `char`-slice patterns.

- The source is split into **lines** (one `AstNode` per non-empty line) by
  scanning for the platform newline: `\r\n` on Windows, `\n` on Linux (selected
  via `#[cfg(target_os = ...)]` at [src/ast.rs:75](src/ast.rs#L75)).
- Each line goes to `alloc_node` ([src/ast.rs:111](src/ast.rs#L111)), which:
  1. skips leading spaces; an all-space line produces **no node**;
  2. dispatches on the trimmed slice — `#!`→`Fail`, `#?`→`Unreachable`,
     `#$ …`→`Define(new_cast(..))`, `#& …`→`Lat(new_lat(..))`,
     `#@ …`→`Region(new_region(..))`, any other `#…`→a dropped comment (no
     node);
  3. otherwise strips any inline `# comment` and passes the code to
     `new_instruction` ([src/ast.rs:215](src/ast.rs#L215)), which matches the
     mnemonic prefix and calls the matching `new_*` constructor;
  4. heap-allocates the node with raw `alloc` + `write` + `NonNull` and links it
     onto the tail.
- Nodes form an **intrusive doubly-linked list** of `AstNode { prev, value, next }`
  ([src/ast.rs:7](src/ast.rs#L7)). `new_ast` returns the head
  (`Option<NonNull<AstNode>>`).

Per-instruction parsers extract operands by **hard-coded character offsets**
(e.g. `lhs = src[0..2]`, `rhs = src[4..6]`, third operand from index 8). This
assumes exactly 2-char register names and `", "` separators — see the parser
limitations in [§9](#9-conventions--gotchas).

### 4.2 Compression — `compress` ([src/lib.rs:18](src/lib.rs#L18))

Walks the linked list into a `Vec`, then `alloc`s a single contiguous
`[AstNode; N]` block and copies every node into it (re-linking `prev`/`next`), so
the AST is cache-friendly for the many traversals the verifier performs. The
head pointer is updated in place. Purely a memory-layout pass; semantics are
unchanged.

<a id="43-verification--explorerer"></a>
### 4.3 Verification — `Explorerer` ([src/verifier.rs:119](src/verifier.rs#L119))

The verifier is an **incremental state machine**. The caller repeatedly calls
`next_step(self) -> ExplorePathResult` (it consumes and returns `self` by move),
each call advancing the exploration by one AST node. It terminates as
`Valid(ValidPathResult)` or `Invalid`.

**The execution tree.** Exploration is recorded as a tree of raw-pointer nodes:

- `VerifierConfiguration` ([src/verifier.rs:34](src/verifier.rs#L34)) — one per
  *system* (an `InnerVerifierConfiguration { sections, harts }`). The root.
- `VerifierNode` ([src/verifier.rs:82](src/verifier.rs#L82)) — one executed
  instruction step: `{ prev, root, hart, node: NonNull<AstNode>, next }`. `hart`
  is which hart executed it.
- `VerifierLeafNode` ([src/verifier.rs:99](src/verifier.rs#L99)) — a frontier
  tip: `{ prev, variable_encounters: Map<Label, *VerifierNode>, hart_fronts: Map<hart, *VerifierNode> }`.
  `variable_encounters` records where each variable was *first* seen on this
  path (used for backtracking); `hart_fronts` the most-recent node per hart.
- `InnerNextVerifierNode::{ Branch(Vec<*VerifierNode>), Leaf(*VerifierLeafNode) }`
  is the forward link.

State is **not** stored at nodes; it is reconstructed on demand by replaying the
path from the root (`find_state`, [src/verifier.rs:1435](src/verifier.rs#L1435)).
This is the acknowledged O(n)-per-step inefficiency (TODO at
[src/verifier.rs:98](src/verifier.rs#L98)).

**Initialization** (`Explorerer::new`): requires every system has `harts > 0`,
then seeds each system (via `build_initial_chain`) with an initial chain of one
`VerifierNode` per hart — all pointing at `start_ptr`, **the first AST node** —
terminated by a `VerifierLeafNode` pushed onto `queue`. There is no `.global`/
`_start:` entry: verification (and execution) starts from the first line, like
Python (the runnable entry is added later by codegen). `configuration` starts
empty.

> Because the first instruction can itself be a variable's first encounter (its
> encounter node is then in the initial chain, with the root as predecessor),
> `invalid_path` detects `encounter.node == start_ptr` and, instead of walking
> back to a predecessor that doesn't exist, rebuilds the whole initial chain with
> `build_initial_chain`. (With an explicit `_start:` label this never happened —
> the label buffered the root from any encounter.)

**One step** (`next_step`, [src/verifier.rs:291](src/verifier.rs#L291)):
1. If `queue` is empty → **`Valid`**: every reachable path under the current
   `configuration` has been validated with no `#!` reached. Returns
   `ValidPathResult { configuration, touched, jumped, accessed }`.
2. Pop (peek) the front leaf; mark its AST node in `touched`.
3. Dispatch on the instruction:
   - **No-op for checking** (`Li`, `Label`, `Addi`, `Blt`, `Csrr`, `Bne`,
     `Bnez`, `Beqz`, `Bge`, `Wfi`, `Beq`, `J`, `Unreachable`, `Region`):
     nothing to check here; their *effects* are applied later by
     `find_state`/`queue_up`.
   - `Define` / `Lat` / `La`: `load_label(..)` —
     [type inference & backtracking](#type-inference--backtracking) below.
     Failure → invalid.
   - `Sw`/`Sb` → `check_store`, `Ld`/`Lw`/`Lb` → `check_load`
     ([src/verifier.rs:728](src/verifier.rs#L728)/[822](src/verifier.rs#L822)):
     reconstruct `State`, read the destination register; if it is a tagged
     `Ptr`, bounds-check `type_size + ptr_offset + insn_offset <= size(type)`;
     if it is a raw `I64` address, find a covering `Section` — one configured on
     the system **or declared by an already-executed `#@`** (the replayed
     `state.memory.sections`) — and check `Permissions`/`volatile`. The section
     must start at/before the access and be large enough
     (`required_size.compare(&s.size)` must be `Less|Equal|Matches`).
     Out-of-bounds / wrong-permission / no-section → invalid: **every memory
     access must be verifiable as safe**, either through a symbolic variable or
     a described raw region.
   - **`Fail` (`#!`)** → **invalid path** immediately: this path reached an
     assertion failure, so the current type configuration is unsound.
4. On success: `queue_up(leaf)` (enqueue successors), `queue.pop_front()`,
   return `Continue(self)`.

<a id="type-inference--backtracking"></a>
**Type/locality inference & backtracking.** Under-specified variables (`_`) are
searched by chronological backtracking:

- `load_label` ([src/verifier.rs:610](src/verifier.rs#L610)): on first encounter
  of a label it builds an iterator `locality_list() × type_list()` (best→worst:
  localities `[Thread, Global]`; scalar types `[U8, I8, U16, I16, U32, I32, U64,
  I64]`), restricted to any explicitly-annotated locality/type, picks the first
  candidate, inserts it into `configuration`, and pushes the label onto the
  `encountered` stack. If the label is already configured it instead *checks*
  the annotation matches (this catches conflicting `#$` defines) — and, for a
  thread-local, records the encountering hart in the `Thread` hart set (each
  recorded hart gets its own `.bss` copy seeded by `State::new`; without this a
  second hart's access would find no memory behind its `MemoryLabel`).
- On any invalid path, `outer_invalid_path`
  ([src/verifier.rs:477](src/verifier.rs#L477)) pops the **most recently**
  encountered variable, calls `invalid_path` to deallocate the subtree from that
  variable's first-encounter node (rebuilding affected leaves), and tries the
  variable's *next* `(locality, type)` candidate. If its iterator is exhausted,
  the variable is dropped and the next-most-recent variable is tried. If the
  `encountered` stack empties → **`Invalid`**: the program has no valid type
  configuration.
- List/union types are **never** explored automatically (infinitely many), so a
  list/union variable must be declared with `#$` (e.g. `#$ welcome _ [u8 u8]`).

**Hart interleaving enumeration** (`queue_up`,
[src/verifier.rs:875](src/verifier.rs#L875)). For each hart's current node a
`followup` closure classifies the next instruction as **racy** or **non-racy**:

- Loads/stores (`Sb`, `Sw`, `Ld`, `Lw`, `Lb`) are racy **iff** the pointer's
  `MemoryLabel` is `Global` (thread-local accesses assert `thart == hart` and
  are non-racy); raw `I64`-addressed accesses are racy; `Wfi` is treated as racy
  (conservative over-approximation, design note at
  [src/verifier.rs:114](src/verifier.rs#L114)); **`#@` (`Region`) is racy** — a
  region only becomes accessible once its declaration executes, so its order
  relative to other harts' raw accesses is observable and collapsing it would
  skip the (invalid) access-before-declaration interleavings; everything else
  is non-racy.
- Conditional branches are resolved *concretely* from the symbolic register
  ranges using `compare`/`compare_scalar` (`RangeOrdering`/`RangeScalarOrdering`);
  `csrr … mhartid` is special-cased (hart 0 vs non-zero). A taken jump records
  the branch node in `jumped`.
- **Interleaving rule:** if *any* hart's next step is non-racy, only that single
  deterministic node is queued (collapsing redundant interleavings — this is
  what bounds the `h^r` blow-up); only when *all* harts' next steps are racy does
  the tree fork into one branch+leaf per hart, enqueuing every interleaving.

**Runtime-accessed byte ranges (dead-data analysis).** While replaying a path,
`find_state_load`/`find_state_store` record every load/store's
`(label, offset.start .. offset.stop + len)` into `State.accessed`
(an `AccessedRanges = BTreeMap<Label, BTreeSet<(u64, u64)>>`), using the full
symbolic offset span so an under-determined access never under-records. The
`Lat` arm maps the generated descriptor tags (`_a`, …) to the symbols codegen
emits (`__<label>_type` / `__<label>_subtypes`) via `State.descriptor_labels`,
so descriptor reads are recorded under names codegen can look up. Each of the
three `find_state` call sites (`check_store`, `check_load`, `queue_up`) merges
`state.accessed` into `Explorerer.accessed` (`merge_accessed`); since replays
cover whole path prefixes and set-union is idempotent, the repeated replays are
harmless, and like `touched` the union only ever grows (entries from abandoned
configurations remain) — an **over-approximation**, which is the sound direction
for dead-data elimination. **Replays exclude the instruction being processed**,
so `check_store`/`check_load` additionally record the *current* instruction's
own bytes directly into `Explorerer.accessed` (via `record_access_into`) when
its check passes — without this, an access whose successors all halt (`#?`) is
never interior to any replay and its bytes would be wrongly elided (pinned by
the `terminal_access` test). Raw (`I64`-addressed) accesses are *not* recorded: they target
heap/MMIO, not generated storage (soundness of trimming therefore **assumes raw
regions never alias generated storage** — see §10). This bookkeeping must never
feed back into exploration control flow.

**Outputs.** A successful proof yields `ValidPathResult`
([src/verifier.rs:1335](src/verifier.rs#L1335)):
`configuration: TypeConfiguration` (inferred type+locality per variable),
`touched: BTreeSet<NonNull<AstNode>>` (every reachable node),
`jumped: BTreeSet<NonNull<AstNode>>` (branches that ever take their jump), and
`accessed: AccessedRanges` (runtime-accessed bytes per region — drives
dead-data elimination in codegen, [§4.8](#48-code-generation--emit_executable-srccodegenrs)).

`Explorerer` owns the whole tree and frees it in a manual `Drop`
([src/verifier.rs:1267](src/verifier.rs#L1267)).

**Determinism.** Exploration is deterministic: it must never let raw allocation
addresses influence control flow. The one place this was violated was
`invalid_path` ([src/verifier.rs:511](src/verifier.rs#L511)), which grouped
backtracked leaves in a `BTreeMap<*mut VerifierNode, _>` — ordered by pointer
value, so the order replacement leaves were re-queued (and thus the whole step
order and total count) varied run-to-run. It now uses an insertion-ordered `Vec`
keyed off the deterministic `queue` iteration. When adding code that iterates
over nodes/leaves, **order by stable keys** (queue position, hart, AST position,
`Label`), never by pointer (`BTreeSet`/`BTreeMap` over `*mut`/`NonNull` orders by
address). The `next_step` determinism hash
([src/verifier.rs:336](src/verifier.rs#L336)) exists to catch regressions here.
Note `touched`/`jumped` are `BTreeSet<NonNull<AstNode>>` (pointer-ordered) but
only ever queried with `.contains()` and iterated as the AST list, so their
ordering is never observed.

### 4.4 Symbolic value & memory model ([src/verifier_types.rs](src/verifier_types.rs))

This module has **no `unsafe`** and no raw pointers (despite the name,
`MemoryPtr`/`NonNullMemoryPtr` are domain value types, *not* `std::ptr::NonNull`).

- **Scalars are inclusive integer ranges.** `MemoryValueI8/I16/I32/I64`,
  `MemoryValueU8/U16/U32/U64` each hold `{ start, stop }` (`start..=stop`),
  unified behind the `RangeType` trait
  ([src/verifier_types.rs:241](src/verifier_types.rs#L241)) which provides
  interval `add`/`sub`, `compare`, `exact()` (Some iff `start==stop`), `any()`
  (full type range, used for unknown memory), and native-endian byte slicing.
- **`MemoryValue`** ([src/verifier_types.rs:661](src/verifier_types.rs#L661)) is
  the universal symbolic value carried in registers and memory:
  scalars, `List(Vec<MemoryValue>)`, `Ptr(MemoryPtr)`, `Csr(CsrValue)`. `Add`
  implements pointer + scalar arithmetic.
- **Pointers are `(MemoryLabel, MemoryValueU64 offset)` pairs**, not addresses,
  so aliasing is reasoned about by *label identity*. `MemoryLabel`
  ([src/verifier_types.rs:1235](src/verifier_types.rs#L1235)) is
  `Global { label }` or `Thread { label, hart }`.
- **Memory** is `MemoryMap` ([src/verifier_types.rs:1260](src/verifier_types.rs#L1260)):
  a `BTreeMap<MemoryLabel, MemoryValue>` (`.bss`/`.data`) plus a `Vec` of raw
  `MemorySection`s with `Section` descriptors (system-configured + `#@`-declared).
  Reads/writes are byte-granular, addressed by `Slice { base, offset, len }`. A
  partial overwrite of a wide scalar **splits** it into a `List` of `U8` ranges
  with the written value spliced in (`MemoryValue::set`,
  [src/verifier_types.rs:871](src/verifier_types.rs#L871)). Raw `I64`-addressed
  stores resolve a `Section`, honour `volatile` (the store is dropped) and
  `permissions`. Non-volatile raw stores maintain a **backing** of
  `MemorySection`s serving two purposes: tracking stored *values* (for future
  content assertions — raw *loads* do not consult it yet; they return a
  full-range value of the loaded width in `find_state_load`) and tracking
  *which bytes are touched*. A store therefore always fills its **maximal
  span** `address.start .. address.stop + len`: backings overlapping the span
  are erased (absent backing reads as fully-unknown — the sound union of "old
  value or new value", allocation-free even for huge symbolic spans), then an
  exactly-addressed store whose value width matches `len` records the new
  bytes. Never silently drop a ranged store — that would leave stale "known"
  values behind.
- **Machine state** is `State { registers: Vec<RegisterValues>, memory,
  configuration, accessed, descriptor_labels }`
  ([src/verifier_types.rs:1503](src/verifier_types.rs#L1503)), one
  `RegisterValues` per hart. `State::new` seeds each configured variable with a
  full-range value (one `.bss` entry per hart for thread-locals). `accessed` /
  `descriptor_labels` are the dead-data bookkeeping described in
  [§4.3](#43-verification--explorerer) (`State::record_access`).
- **`TypeConfiguration`** ([src/verifier_types.rs:1598](src/verifier_types.rs#L1598))
  = `BTreeMap<Label, (LabelLocality, Type)>`. `LabelLocality::Thread(BTreeSet<u8>)`
  records exactly which harts need a copy of a thread-local. `insert` enforces
  that all harts agree on a thread variable's `Type` and unions the hart set;
  `Global` labels must be unique.

### 4.5 Runtime type reflection — the `#&` / `lat` mechanism

`#& reg, label` loads a pointer to a **runtime type descriptor** that the
verified program can inspect (this is how the example programs check that
`welcome` is a `u8` list at runtime). `MemoryMap::set_type`
([src/verifier_types.rs:1379](src/verifier_types.rs#L1379)) lowers a (possibly
nested) `Type` into in-memory records. Each type becomes a **4-field list**:

```
[ u64 type-number, ptr-to-subtypes, u64 length, u8 locality ]
```

The *type-number* is `FlatType as u64` ([src/ast.rs:276](src/ast.rs#L276)):
`U8=0, I8=1, U16=2, I16=3, U32=4, I32=5, U64=6, I64=7, List=8, Union=9`. This is
the `li t2, 8 # list type number` you see in [assets/uart_hello.s](assets/uart_hello.s).
Nested lists are emitted as separate labelled records linked by `Ptr`; leaf
(non-list) types carry a null pointer and length 0. The schema of each record is
`memory_value_type_of()` = `List([U64, U64, U64, U8])`.

### 4.6 Optimization ([src/optimizer.rs](src/optimizer.rs))

Driven by the `ValidPathResult` sets, after a successful proof:

- `remove_untouched(ast, touched)` ([src/optimizer.rs:7](src/optimizer.rs#L7)) —
  unlinks and `dealloc`s every node **not** in `touched` (dead-code elimination).
- `remove_branches(ast, jumped)` ([src/optimizer.rs:30](src/optimizer.rs#L30)) —
  removes conditional branch instructions (`Bne`, `Blt`, `Beq`, `Beqz`, `Bnez`,
  `Bge`) **not** in `jumped` (a branch the verifier proved never jumps is dead).

Both rewrite the head pointer when the first node is removed.

### 4.7 Serialization — `print_ast` ([src/lib.rs:62](src/lib.rs#L62))

Walks the list and `Display`-formats each `Instruction`. The `Display` impls in
[src/ast.rs](src/ast.rs) define the **canonical text form**: registers print as
ABI names, immediates honour their stored radix (decimal or `0x`), loads print
`to, offset(from)`, stores print `from, offset(to)`, `#$`/`#&`/`#!`/`#?` print
their directive forms. On Windows it emits `\r\n`. This canonical form is what
the `uart_hello` test compares against [assets/uart_hello_ast.s](assets/uart_hello_ast.s) — note
e.g. `(t0)` is normalized to `0(t0)`.

### 4.8 Code generation — `emit_executable` ([src/codegen.rs](src/codegen.rs))

Lowers the verified + optimized AST plus the inferred `TypeConfiguration` into a
**complete, runnable RISC-V program** (a `String`). This is the language's core
idea realized: the input leaves the memory layout implicit, the verifier infers
it, and codegen materializes it. It does **not** go through `print_ast` (which
emits the dialect verbatim for the test assertions); it walks the AST itself:

- Emits the `.global _start` / `_start:` entry the linker needs (the input has no
  explicit entry — execution begins at the first instruction, where verification
  began).
- Lowers the directives: `#$` (define) and `#@` (region) → kept as comments
  (both are compile-time metadata); `#& reg, label` (lat) → `la reg,
  __<label>_type` (load the generated descriptor's address); `#!` (fail) →
  `ebreak`; `#?` (unreachable / end) → jump to a `__halt: wfi; j __halt` loop
  appended after `.text`.
- Emits `.data` — the runtime **type descriptors** read via `#&`, as 25-byte
  records `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]` (the
  same layout §4.5 builds in `set_type`; deliberately unpadded so the programs
  can stride them by 25) — **minus the bytes the program never accesses at
  runtime** (next bullet).
- **Dead-data elimination.** `emit_executable` takes the proof's
  `accessed: AccessedRanges` and emits only runtime-accessed descriptor bytes
  (`Coverage` / `emit_descriptor_record`): a live field is emitted with its
  value; a dead field below the region's last live byte becomes `.zero` padding
  (the 25-byte stride is hardcoded in the programs, so interior offsets must
  hold); trailing dead bytes are **omitted**. Concretely, in `uart_hello` every
  record's locality byte (offset 24) vanishes — `__welcome_type` is 24 bytes
  and `__welcome_subtypes` is 33 (`.dword`, `.zero 17` padding, `.dword`) —
  because the programs only consult locality through the verifier at compile
  time. Information only read at compile time does not exist in the output.
- Emits `.bss` — zero-initialized storage for every inferred variable, sized by
  `size(type)`.

**Toolchain gotchas** (see [scripts/build-run.sh](scripts/build-run.sh)):
- Link with **`--no-relax`**. Otherwise the linker relaxes `la value` into
  `addi t0, gp, …` (global-pointer-relative), but a bare-metal program has no
  `gp` (it is 0), so the address is garbage and the first store faults.
- QEMU `virt` with `-bios none -kernel` loads at `0x80000000`, so link with
  `-Ttext=0x80000000 -e _start`. The 25-byte (unaligned) descriptor records rely
  on QEMU emulating misaligned `ld`.

The `racy_increment`/`racy_store_inferred`/`racy_store_annotated`/`uart_hello`/`heap_regions` integration tests do this
**automatically**: each pins the exact emitted program, lowers it to
`target/gen/<name>.s` and, via the `run_program`/`run_in_qemu` helpers in
`tests/common/mod.rs`, assembles + links + boots it under WSL, asserting **no
CPU fault** (and that `uart_hello` writes `H` to the UART). The toolchain and QEMU
are **required** — the tests **fail** (not skip) if WSL / the toolchain / QEMU
are absent; point `RISCV_BIN` at the toolchain `bin/` (default
`$HOME/riscv-toolchain/riscv/bin`). [scripts/build-run.sh](scripts/build-run.sh)
does the same by hand from the generated files.

## 5. The language dialect (as actually parsed)

- **Directives**: `#!` `Fail`, `#?` `Unreachable`, `#$ <label> <locality> <type>`
  `Define`, `#& <reg>, <label>` `Lat`, `#@ <start> <end> <perms>` `Region`
  (declare an accessible memory region: bounds are immediates or registers,
  `end` exclusive, perms `r`/`w`/`rw`; executed in program order, so an
  allocator can declare each allocation as it makes it). Plain `#…` comments and
  inline `# …` comments are stripped.
- **Instructions** (`Instruction` enum, [src/ast.rs:176](src/ast.rs#L176), 25
  variants): `csrr`, `bnez`, `j`, `wfi`, labels (`foo:`), `.global`, `.data`,
  `.ascii` (parser is `todo!()`), `la`, `li`, `sw`, `lw`, `addi`, `blt`, `lb`,
  `beqz`, `sb`, `bge`, `ld`, `bne`, `beq`, plus the directives above.
- **Registers** (`new_register`, [src/ast.rs:1097](src/ast.rs#L1097)): **only**
  `t0`–`t5`, `a0`, `a1` are parseable, despite the full `X0`–`X31` enum existing
  for `Display`. Other register names cause `.unwrap()` panics at call sites.
- **CSRs**: only `mhartid`.
- **Types**: scalars `u8/i8/u16/i16/u32/i32/u64/i64`, `List` `[t t …]`, `Union`
  `{t t …}`.
- **Localities**: `global`, `thread` (and `_` = infer).

## 6. Integration tests ([tests/](tests/))

The tests are **integration tests** (one binary per file), so they can only use
the crate's public API — this is why the pipeline lives in the library and
everything the tests need is `pub` / re-exported at the crate root.

`tests/common/mod.rs` (included by each test via `mod common;`) holds the shared
helpers:
- `setup_test(asm) -> Option<NonNull<AstNode>>` — reads `assets/<asm>.s`
  (resolved against `CARGO_MANIFEST_DIR`) and runs `new_ast` + `compress`.
- `trace_valid_path(explorerer) -> (Vec<String>, Result<ExplorePathResult, CompilerError>)`
  — steps the verifier to a terminal state, returning one **exact trace line per
  step** (see below) plus the terminal outcome: `Ok` of the terminal
  `ExplorePathResult` (`Valid`/`Invalid`), or `Err` of the [`CompilerError`] the
  verifier hit. The trace is returned in **all** cases (including error), with the
  failing step appended as the last line, so a test can show *where* it stopped.
- `expect_valid(trace, result) -> ValidPathResult` — asserts `Ok(Valid(_))`,
  else panics with the outcome and the tail of the trace.
- `front_step(explorerer)` — reads the front queue leaf to report the
  `(hart, harts, instruction)` the next step will process.
- `config_timeline(trace)` — the sequence of distinct, consecutive `configuration`
  strings: i.e. the type-inference timeline (a reset to `Config: []` marks a
  backtrack).
- `assert_trace(actual, expected)` — compares a trace line-for-line, reporting
  the first diverging step index.
- `normalize(s)` — collapses `\r\n` → `\n` so the `\n`-based expected strings
  compare regardless of the platform line ending `print_ast` emits.
- `verify_and_optimize(name, sections, harts)` — the whole pipeline (parse →
  compress → verify → `remove_untouched`/`remove_branches`) →
  `(ast, configuration, accessed)`.
- `run_program(name, ast, configuration, accessed)` / `run_in_qemu(name, asm)` —
  lower the optimized program with `emit_executable`, assert **no
  compile-time-only data leaked** (no `.byte` locality directives survive in the
  generated `.data`/`.bss` — none of these programs read locality at runtime),
  then assemble + link + **boot it in QEMU under WSL**, asserting no CPU fault
  and returning the captured UART output. The toolchain + QEMU are **required**:
  these panic (fail the test) if WSL / the toolchain / QEMU are missing (see §4.8).

A trace line is `h<hart>/<harts> | <instruction> | <config> | q<n> t<n> j<n>`
(the instruction being processed this step, and the resulting configuration /
queue / touched / jumped state).

Each test verifies via `trace_valid_path`, asserts the inferred `configuration`
and the `accessed` byte ranges, runs `remove_untouched` / `remove_branches`,
asserts `normalize(print_ast(ast))` after each, asserts the **exact emitted
program** (`emit_executable`), and finally `run_program`s the result (boots it
in QEMU). The **incremental** assertions differ by test:
- `racy_store_inferred` — racy store of `0` to `value` (type `_`, inferred). Asserts the **full
  82-step trace** (`assert_trace`): the type search `Gu8 → Gi8 → Gu16 → Gi16 →
  Gu32` (config resets to `[]` at each failing `sw`), then the 2-hart racy
  interleavings fanning the queue out to 6 and draining to 0.
- `racy_store_annotated` — same program as `racy_store_inferred` but with explicit `#$ value global u32`, so the
  annotation is *checked*, never searched. Asserts the **full 54-step trace**.
- `racy_increment` — racy increment of `value` (type `_`); its interleaving fan-out is 603
  steps (too many to assert line-for-line, so `racy_store_inferred`/`racy_store_annotated` pin the per-step
  shape). Asserts the exact step **count**, the `config_timeline`
  (`Gu8 → … → Gu32`) and the optimized output.
- `uart_hello` — full UART "Hello, World!" with list-type checking; 20464 steps.
  Asserts the AST round-trips to [assets/uart_hello_ast.s](assets/uart_hello_ast.s), the
  exact step **count**, the `config_timeline` (value search, then `welcome`'s
  `[u8 u8]` joins),
  `{ value: (Global, U32), welcome: (Thread({0}), List([U8, U8])) }`, the exact
  `accessed` ranges (descriptor reads at offsets 0/8/16 of `__welcome_type` and
  0/25 of `__welcome_subtypes` — never a locality byte), and the **exact
  generated program** including the dead-data-eliminated `.data` (24-byte
  `__welcome_type`, 33-byte `__welcome_subtypes` with `.zero 17` padding, no
  `.byte` anywhere).
- `heap_regions` ([assets/heap_regions.s](assets/heap_regions.s)) — `#@` region declarations
  (immediate bounds accessed at a non-zero offset, and register bounds exactly
  as wide as the store that hits them — the latter would panic in
  `MemoryMap::set` if it re-checked with the value's width instead of the
  instruction's) with racy raw stores/loads inside them; 1021 steps (`#@` is
  racy, so its interleavings against the accesses are explored). Asserts the
  round-trip (including both `#@` forms), empty `configuration`/`accessed`, the
  exact emitted program (no `.data`/`.bss` at all), and boots it in QEMU.
- `raw_access_undeclared` ([assets/raw_access_undeclared.s](assets/raw_access_undeclared.s)) — loads from a raw address no `#@`
  region or section describes. Asserts the exact 2-step prefix trace and that
  the terminal outcome is **`Invalid`**: every memory access must be verifiable
  as safe.
- `region_overrun` ([assets/region_overrun.s](assets/region_overrun.s)) — a 4-byte store into a 2-byte `#@`
  region. Asserts the exact 3-step prefix trace and the **`Invalid`** outcome,
  pinning the *direction* of the section bounds check (`required_size <=
  s.size`; with the operands swapped this would wrongly verify).
- `terminal_access` ([assets/terminal_access.s](assets/terminal_access.s)) — a descriptor load whose only successor
  is `#?` (a path-terminal access, never interior to any replay). Asserts the
  full 4-step trace, that `accessed` still contains the load's bytes (the
  check-time record in `check_load` — without it dead-data elimination would
  emit a descriptor the program reads but that has no bytes), the exact emitted
  program (`__value_type` keeps its 8 live bytes, drops the other 17), and
  boots it in QEMU.
- `unsupported_construct` ([assets/unsupported_construct.s](assets/unsupported_construct.s)) — a `.global` directive, which the
  verifier does not model (programs have no explicit entry). Asserts that
  `trace_valid_path` returns `Err(CompilerError::Unsupported(_))` (rather than
  panicking) **and** that the trace's last line is the failing step — the
  error-path analogue of the success tests.

Behaviour-focused tests (each pins one specific rule or error case; the Valid
ones also pin the exact emitted program, and all Invalid ones pin their trace
prefix):
- `vague_access` — `record_access` with a *range* offset fills the maximal span
  (a 4-byte store at offset `0..=6` records `(0, 10)`), and a recorded range
  that only partially overlaps a descriptor field emits the **whole** field
  (no sub-field elision) — the soundness contract of dead-data elimination.
- `partial_variable_access` — accesses only bytes 0 and 2 of a `[u8 u8 u8 u8]`;
  `accessed` records exactly `(0,1)`/`(2,3)` while `.bss` storage keeps the
  full 4 bytes (unaccessed live storage is never trimmed). 14 steps; boots.
- `descriptor_read_union` — hart 0 reads a descriptor's type-number, hart 1 its
  length; `accessed` is the union, so both fields are emitted with interior
  `.zero 8` padding between them and an empty subtypes array. 43 steps; boots.
- `locality_runtime_read` — the inverse of the elision rule: `lb` of the
  locality byte (offset 24) at runtime keeps the `.byte 1` in `.data` behind
  `.zero 24` padding (bypasses `run_program`'s no-`.byte` assert). Boots.
- `offset_widened_inference` — a 4-byte store at offset 2 forces the type
  search through `u8…i32` to `u64` (the offset participates in inference);
  `accessed` is exactly `(2, 6)`. 29 steps; boots.
- `conflicting_defines` / `annotated_store_overflow` — contradictory `#$`
  defines / a `sw` into an annotated `u8`: annotated searches have one
  candidate, so backtracking exhausts → **`Invalid`**.
- `region_permissions` (assets `region_read_only.s`/`region_write_only.s`) —
  store into an `r` region / load from a `w` region → **`Invalid`**.
- `region_declared_late` — the store precedes its `#@` in program order;
  regions take effect when executed (declare-before-use) → **`Invalid`**.

Because exploration is deterministic (see the determinism note in
[§4.3](#43-verification--explorerer)), the step counts and full traces are stable
contracts — re-derive them when behaviour legitimately changes; do not loosen
them to absorb a regression.

`two.rs` (obsolete API, ended in `todo!()`) and the old `src/tests/` unit-test
module have been **deleted**.

## 7. Verification complexity

From [language.md](language.md): worst case `O(n · h^r · 2^b · 8^v)` where
`n` = instructions, `h` = harts, `r` = racy instructions, `b` = indeterminate
branches, `v` = unspecified variables. The non-racy interleaving collapse
(`queue_up`) and chronological type backtracking are the mechanisms that keep
real programs far under this bound. `8` is the count of scalar types in
`type_list()`; `2` reflects branch outcomes; `h^r` the racy interleavings.

## 8. Key data structures (quick reference)

| Type | Location | Purpose |
|------|----------|---------|
| `AstNode` / `AstValue` / `Span` | [ast.rs:7](src/ast.rs#L7) | Intrusive AST list node, value, source span. |
| `Instruction` | [ast.rs:176](src/ast.rs#L176) | 25-variant tagged union of supported instructions/directives. |
| `Region` / `RegionBound` / `RegionPermissions` | [ast.rs](src/ast.rs) | The `#@` directive: region bounds (immediate/register) + `r`/`w`/`rw`. |
| `Type` / `FlatType` / `Locality` | [ast.rs:332](src/ast.rs#L332) / [276](src/ast.rs#L276) / [313](src/ast.rs#L313) | Compile-time types; `FlatType` is the runtime type-number encoding. |
| `Explorerer` | [verifier.rs:119](src/verifier.rs#L119) | The verification state machine. |
| `VerifierNode` / `VerifierLeafNode` | [verifier.rs:82](src/verifier.rs#L82) / [99](src/verifier.rs#L99) | Execution-tree interior / frontier nodes. |
| `ExplorePathResult` | [verifier.rs:1293](src/verifier.rs#L1293) | `Valid` / `Invalid` / `Continue(self)`. |
| `ValidPathResult` | [verifier.rs:1335](src/verifier.rs#L1335) | `{ configuration, touched, jumped, accessed }` — feeds the optimizer + codegen. |
| `AccessedRanges` | [verifier_types.rs](src/verifier_types.rs) | `BTreeMap<Label, BTreeSet<(u64, u64)>>` — runtime-accessed bytes per region; drives dead-data elimination. |
| `InnerVerifierConfiguration` / `Section` / `Permissions` | [verifier.rs:40](src/verifier.rs#L40) / [46](src/verifier.rs#L46) / [53](src/verifier.rs#L53) | Per-system input: harts + memory map. |
| `MemoryValue` | [verifier_types.rs:661](src/verifier_types.rs#L661) | Universal symbolic value (ranges / list / ptr / csr). |
| `MemoryLabel` / `MemoryPtr` | [verifier_types.rs:1235](src/verifier_types.rs#L1235) / [1189](src/verifier_types.rs#L1189) | Label-tagged symbolic memory & pointers. |
| `State` / `MemoryMap` / `RegisterValues` | [verifier_types.rs:1503](src/verifier_types.rs#L1503) / [1260](src/verifier_types.rs#L1260) / [1552](src/verifier_types.rs#L1552) | Reconstructed machine state. |
| `TypeConfiguration` / `LabelLocality` | [verifier_types.rs:1598](src/verifier_types.rs#L1598) / [1573](src/verifier_types.rs#L1573) | Inferred per-variable type+locality; the proof output. |

## 9. Conventions & gotchas

- **Pervasive `unsafe` raw-pointer linked lists.** Both the AST
  (`Option<NonNull<AstNode>>`) and the verifier tree (`*mut VerifierNode` etc.)
  are hand-managed: `alloc`/`Box::into_raw` to allocate, manual `dealloc` to
  free. Correctness depends on hand-maintained invariants (e.g. exactly one node
  per hart before the root; the head/tail pointers are accurate). Almost every
  verifier function is `unsafe`.
- **Debug-only infinite-loop guards.** Many `while` loops over the lists carry
  `#[cfg(debug_assertions)] let mut check = (0..1000).into_iter();` with
  `debug_assert!(check.next().is_some());` (and `(0..100_000)` in a couple of
  places). These panic in debug builds if a loop exceeds the bound (cycle /
  corruption guard) and are **compiled out in release** — release builds can loop
  unboundedly on malformed structures. Preserve these when adding new traversals.
- **Error model — `verifier.rs` never panics.** Every former
  `todo!`/`unimplemented!`/`unreachable!`/`panic!`/`unwrap`/`expect` in
  [src/verifier.rs](src/verifier.rs) has been converted to return a
  [`CompilerError`](src/verifier.rs) (`Unsupported(String)` for a construct the
  verifier does not yet handle — the old `todo!`s; `Internal(String)` for a
  violated invariant — the old `unwrap`/`unreachable`/`panic`). `Explorerer::new`
  and `next_step` therefore return `Result<_, CompilerError>`, and the failure
  propagates to the caller (e.g. a test) alongside the trace, instead of aborting
  the process. A module-level `#![deny(clippy::unwrap_used, clippy::expect_used,
  clippy::panic, clippy::todo, clippy::unimplemented, clippy::unreachable)]` at
  the top of the file enforces this — keep `verifier.rs` clippy-clean.
  - Helpers: `OrInternal::internal("ctx")?` converts an `Option`/`Result` into a
    `CompilerError::Internal` (the `?`-able replacement for `.unwrap()`);
    `check_store`/`check_load` return `Result<ControlFlow<ExplorePathResult,
    Self>, CompilerError>` (continue / terminal-outcome in `Ok`, error in `Err`).
  - **Still panics: [src/verifier_types.rs](src/verifier_types.rs).** The
    value/memory model (and the parser in [src/ast.rs](src/ast.rs)) have **not**
    been converted — their internal `todo!`/`unwrap` still abort. A program that
    reaches one of those (e.g. unions, multi-element list slices, `.ascii`) will
    panic before `verifier.rs` can turn it into a `CompilerError`. Converting
    these is the remaining work to make the whole pipeline panic-free.
- **Parser fragility.** Operands are sliced at fixed offsets (2-char registers,
  single space after commas); only 8 register names parse; `Span::row`/`column`
  re-read the whole source file from disk on every call and `.unwrap()` the IO.
- **Windows newlines.** Parsing and `print_ast` both special-case `\r\n`; the
  tests normalize via `normalize()` so the `\n`-based expected strings are
  portable. The canonical printed form makes the zero offset explicit
  (`sw t1, (t0)` parses and prints back as `sw t1, 0(t0)`), so expected strings
  must use `0(t0)`, matching [assets/uart_hello_ast.s](assets/uart_hello_ast.s).
- **Tests pin exact incremental behaviour — brittle by design.** `racy_store_inferred`/`racy_store_annotated`
  assert the full per-step trace; `racy_increment`/`uart_hello` assert the exact step count and
  type-inference timeline; all assert the exact `TypeConfiguration` and optimized
  `print_ast` output. A behavioural change to parsing, inference, interleaving or
  optimization will (correctly) break them; re-baseline deliberately (re-derive
  the expected values from the new behaviour), never by loosening the assertions.
  These are stable contracts only because exploration is deterministic — keep it
  that way (see the determinism note in [§4.3](#43-verification--explorerer)).
- **Manual `dealloc` layouts must match the type.** `invalid_path`'s
  encounter-subtree DFS frees `VerifierNode`s and `VerifierLeafNode`s with
  *different* sizes — each must use its own `Layout`. (A prior bug freed a
  `*mut VerifierNode` with `Layout::new::<VerifierLeafNode>()`; benign while
  exploration rarely backtracked at the root, but it corrupted the heap once
  first-line encounters made root rebuilds frequent. Now fixed — keep node and
  leaf deallocations on their own layouts.)
- **`accessed` is bookkeeping, never control flow.** The dead-data ranges
  (`State.accessed` → `Explorerer.accessed`) must stay an over-approximating
  union: record with the full symbolic offset span (`offset.start ..
  offset.stop + len`), merge at every `find_state` call site, and never branch
  on the contents during exploration (that would couple step order to
  bookkeeping and could break determinism). When adding a new load/store form,
  add its `record_access` call — a missed record means codegen may elide a live
  byte, which produces a *wrong program*, not a test failure.
- **`From<MemoryValue> for Type` vs `From<&MemoryValue> for Type`** disagree for
  `Ptr` (`I64` by value, `U64` by reference) — be deliberate about which you call.
- **`Locality` discriminants are reversed** vs declaration order
  (`Thread = 1`, `Global = 0`).
- **Stray output**: an unconditional `println!` debug block sits in
  `MemoryValue::set` near [src/verifier_types.rs:1050](src/verifier_types.rs#L1050).

## 10. Known limitations & TODO map

The most impactful in-code TODOs/limitations (search the files for the rest):

- Wire the verifier into the binary: replace the `todo!()` in
  [src/main.rs](src/main.rs) and stop hard-coding `assets/two.s` (which the
  parser cannot read anyway). The verifier currently runs only via the
  integration tests.
- State caching so `find_state` doesn't replay the path every step
  ([verifier.rs:98](src/verifier.rs#L98), [879](src/verifier.rs#L879)).
- Raw-`I64`-address **loads** always read as a full-range (unknown) value of
  the loaded width — stored values are not tracked through heap memory, so a
  program cannot yet *branch* on a value it stored to a `#@` region (the
  comparison is indeterminate → `Unsupported`).
- Register-defined `#@` bounds use plain interval arithmetic (`end - start`),
  which loses the correlation between the two bounds: regions with genuinely
  under-determined bases verify conservatively (or hit the indeterminate
  section comparison). Relational tracking is future work — today an
  allocator's `#@ t0 t1 rw` works when the bounds are path-exact.
- Dead-data elimination only trims the **descriptor** regions; `.bss` variable
  storage is still emitted at full `size(type)` even if only some bytes are
  accessed. The mechanism (per-label `accessed` ranges) already covers variable
  labels, so extending it is codegen-only work.
- **Raw regions are assumed disjoint from generated storage.** Raw (`#@` /
  section) accesses are not recorded in `accessed`, and nothing verifies a
  declared region does not physically overlap the linker-placed `.data`/`.bss`
  (whose layout additionally shifts with dead-data elimination). A raw store
  into that overlap would invalidate bytes the model treats as label-only.
  Either verify declared regions against the emitted address range or document
  the obligation per program.
- **Nested-list descriptors cannot be emitted.** `set_type` models them (one
  generated tag per `List` node) and the `Lat` arm conflates all subtype tags
  under one `__<label>_subtypes` accessed-key (sound, over-records), but
  codegen's `leaf_record_fields` emits `.dword 0` for a nested record's
  subtypes pointer — a verified program that follows it would dereference 0 at
  runtime. Emitting nested descriptors (or rejecting them in codegen) is open.
- Multi-element list slice get/set returns `ListMultiple` (unimplemented;
  `covers` is collected but never applied).
- `.ascii` parsing (`new_ascii`) is entirely `todo!()`.
- `wfi` is modeled as racy (over-approximation → some valid programs rejected,
  slower exploration); interrupt state is unmodeled.
- `partial`/`sequential`/`typed`/`racy-groups` compiler modes and the
  list/union exploration CLI args (`list_depth`, `list_width`, `union_depth`) in
  [language.md](language.md) are designed but not implemented.
