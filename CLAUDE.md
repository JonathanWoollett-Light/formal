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
  tests in [tests/](tests/) (`three`/`four`/`five`/`six`), which parse, verify
  and optimize the example programs and assert the inferred `TypeConfiguration`,
  the optimized output, and the **exact incremental** behaviour of the state
  machine (a full per-step trace for `five`/`six`; the exact step count and
  type-inference timeline for `four`/`three`). See
  [§6](#6-integration-tests-tests).
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
cargo test --test three     # run a single integration-test binary
cargo test --test three -- --nocapture   # with stdout passthrough
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
| [tests/](tests/) | Integration tests: `common/mod.rs` helpers + `three/four/five/six.rs`, `error.rs` (one binary each). Each of `three/four/five/six` also lowers its output and **boots it in QEMU**. |
| [scripts/build-run.sh](scripts/build-run.sh) | Assemble + link (`as`/`ld`) the generated `target/gen/*.s` and boot in QEMU. |
| [assets/](assets/) | Example programs `*.s`; `three_ast.s` is the golden parsed/compressed form of `three.s`. |
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
     `#$ …`→`Define(new_cast(..))`, `#& …`→`Lat(new_lat(..))`, any other
     `#…`→a dropped comment (no node);
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
   `ValidPathResult { configuration, touched, jumped }`.
2. Pop (peek) the front leaf; mark its AST node in `touched`.
3. Dispatch on the instruction:
   - **No-op for checking** (`Li`, `Label`, `Addi`, `Blt`, `Csrr`, `Bne`,
     `Bnez`, `Beqz`, `Bge`, `Wfi`, `Beq`, `J`, `Unreachable`): nothing to check
     here; their *effects* are applied later by `find_state`/`queue_up`.
   - `Define` / `Lat` / `La`: `load_label(..)` —
     [type inference & backtracking](#type-inference--backtracking) below.
     Failure → invalid.
   - `Sw`/`Sb` → `check_store`, `Ld`/`Lw`/`Lb` → `check_load`
     ([src/verifier.rs:728](src/verifier.rs#L728)/[822](src/verifier.rs#L822)):
     reconstruct `State`, read the destination register; if it is a tagged
     `Ptr`, bounds-check `type_size + ptr_offset + insn_offset <= size(type)`;
     if it is a raw `I64` address, find a covering `Section` and check
     `Permissions`/`volatile`. Out-of-bounds / wrong-permission / no-section →
     invalid.
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
  the annotation matches (this catches conflicting `#$` defines).
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
  [src/verifier.rs:114](src/verifier.rs#L114)); everything else is non-racy.
- Conditional branches are resolved *concretely* from the symbolic register
  ranges using `compare`/`compare_scalar` (`RangeOrdering`/`RangeScalarOrdering`);
  `csrr … mhartid` is special-cased (hart 0 vs non-zero). A taken jump records
  the branch node in `jumped`.
- **Interleaving rule:** if *any* hart's next step is non-racy, only that single
  deterministic node is queued (collapsing redundant interleavings — this is
  what bounds the `h^r` blow-up); only when *all* harts' next steps are racy does
  the tree fork into one branch+leaf per hart, enqueuing every interleaving.

**Outputs.** A successful proof yields `ValidPathResult`
([src/verifier.rs:1335](src/verifier.rs#L1335)):
`configuration: TypeConfiguration` (inferred type+locality per variable),
`touched: BTreeSet<NonNull<AstNode>>` (every reachable node), and
`jumped: BTreeSet<NonNull<AstNode>>` (branches that ever take their jump).

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
  `MemorySection`s with `Section` descriptors. Reads/writes are byte-granular,
  addressed by `Slice { base, offset, len }`. A partial overwrite of a wide
  scalar **splits** it into a `List` of `U8` ranges with the written value
  spliced in (`MemoryValue::set`,
  [src/verifier_types.rs:871](src/verifier_types.rs#L871)). Raw `I64`-addressed
  stores resolve a `Section`, honour `volatile` (the store is dropped) and
  `permissions`.
- **Machine state** is `State { registers: Vec<RegisterValues>, memory, configuration }`
  ([src/verifier_types.rs:1503](src/verifier_types.rs#L1503)), one
  `RegisterValues` per hart. `State::new` seeds each configured variable with a
  full-range value (one `.bss` entry per hart for thread-locals).
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
the `li t2, 8 # list type number` you see in [assets/three.s](assets/three.s).
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
the `three` test compares against [assets/three_ast.s](assets/three_ast.s) — note
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
- Lowers the directives: `#$` (define) → kept as a comment; `#& reg, label`
  (lat) → `la reg, __<label>_type` (load the generated descriptor's address);
  `#!` (fail) → `ebreak`; `#?` (unreachable / end) → jump to a `__halt: wfi; j
  __halt` loop appended after `.text`.
- Emits `.data` — the runtime **type descriptors** read via `#&`, as 25-byte
  records `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]` (the
  same layout §4.5 builds in `set_type`; deliberately unpadded so the programs
  can stride them by 25).
- Emits `.bss` — zero-initialized storage for every inferred variable, sized by
  `size(type)`.

**Toolchain gotchas** (see [scripts/build-run.sh](scripts/build-run.sh)):
- Link with **`--no-relax`**. Otherwise the linker relaxes `la value` into
  `addi t0, gp, …` (global-pointer-relative), but a bare-metal program has no
  `gp` (it is 0), so the address is garbage and the first store faults.
- QEMU `virt` with `-bios none -kernel` loads at `0x80000000`, so link with
  `-Ttext=0x80000000 -e _start`. The 25-byte (unaligned) descriptor records rely
  on QEMU emulating misaligned `ld`.

The `four`/`five`/`six`/`three` integration tests do this **automatically**: each
lowers its output to `target/gen/<name>.s` and, via the `run_program`/`run_in_qemu`
helpers in `tests/common/mod.rs`, assembles + links + boots it under WSL,
asserting **no CPU fault** (and that `three` writes `H` to the UART). The toolchain
and QEMU are **required** — the tests **fail** (not skip) if WSL / the toolchain /
QEMU are absent; point `RISCV_BIN` at the toolchain `bin/` (default
`$HOME/riscv-toolchain/riscv/bin`). [scripts/build-run.sh](scripts/build-run.sh)
does the same by hand from the generated files.

## 5. The language dialect (as actually parsed)

- **Directives**: `#!` `Fail`, `#?` `Unreachable`, `#$ <label> <locality> <type>`
  `Define`, `#& <reg>, <label>` `Lat`. `#@`/`section` is in the design notes but
  **not parsed**. Plain `#…` comments and inline `# …` comments are stripped.
- **Instructions** (`Instruction` enum, [src/ast.rs:176](src/ast.rs#L176), 24
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
  compress → verify → `remove_untouched`/`remove_branches`) → `(ast, configuration)`.
- `run_program(name, ast, configuration)` / `run_in_qemu(name, asm)` — lower the
  optimized program with `emit_executable`, then assemble + link + **boot it in
  QEMU under WSL**, asserting no CPU fault and returning the captured UART output.
  The toolchain + QEMU are **required**: these panic (fail the test) if WSL / the
  toolchain / QEMU are missing (see §4.8).

A trace line is `h<hart>/<harts> | <instruction> | <config> | q<n> t<n> j<n>`
(the instruction being processed this step, and the resulting configuration /
queue / touched / jumped state).

Each test verifies via `trace_valid_path`, asserts the inferred `configuration`,
runs `remove_untouched` / `remove_branches`, asserts `normalize(print_ast(ast))`
after each, and finally `run_program`s the result (boots it in QEMU). The
**incremental** assertions differ by test:
- `five` — racy store of `0` to `value` (type `_`, inferred). Asserts the **full
  93-step trace** (`assert_trace`): the type search `Gu8 → Gi8 → Gu16 → Gi16 →
  Gu32` (config resets to `[]` at each failing `sw`), then the 2-hart racy
  interleavings fanning the queue out to 6 and draining to 0.
- `six` — same program as `five` but with explicit `#$ value global u32`, so the
  annotation is *checked*, never searched. Asserts the **full 57-step trace**.
- `four` — racy increment of `value` (type `_`); its interleaving fan-out is 614
  steps (too many to assert line-for-line, so `five`/`six` pin the per-step
  shape). Asserts the exact step **count**, the `config_timeline`
  (`Gu8 → … → Gu32`) and the optimized output.
- `three` — full UART "Hello, World!" with list-type checking; ~20475 steps.
  Asserts the AST round-trips to [assets/three_ast.s](assets/three_ast.s), the
  exact step **count**, the `config_timeline` (value search, then `welcome`'s
  `[u8 u8]` joins), and
  `{ value: (Global, U32), welcome: (Thread({0}), List([U8, U8])) }`.
- `error` ([assets/error.s](assets/error.s)) — loads from a raw (non-label)
  address, which the verifier does not model. Asserts that `trace_valid_path`
  returns `Err(CompilerError::Unsupported(_))` (rather than panicking) **and**
  that the trace's last line is the failing `lw` step — the error-path analogue
  of the success tests.

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
| `Instruction` | [ast.rs:176](src/ast.rs#L176) | 24-variant tagged union of supported instructions/directives. |
| `Type` / `FlatType` / `Locality` | [ast.rs:332](src/ast.rs#L332) / [276](src/ast.rs#L276) / [313](src/ast.rs#L313) | Compile-time types; `FlatType` is the runtime type-number encoding. |
| `Explorerer` | [verifier.rs:119](src/verifier.rs#L119) | The verification state machine. |
| `VerifierNode` / `VerifierLeafNode` | [verifier.rs:82](src/verifier.rs#L82) / [99](src/verifier.rs#L99) | Execution-tree interior / frontier nodes. |
| `ExplorePathResult` | [verifier.rs:1293](src/verifier.rs#L1293) | `Valid` / `Invalid` / `Continue(self)`. |
| `ValidPathResult` | [verifier.rs:1335](src/verifier.rs#L1335) | `{ configuration, touched, jumped }` — feeds the optimizer. |
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
  must use `0(t0)`, matching [assets/three_ast.s](assets/three_ast.s).
- **Tests pin exact incremental behaviour — brittle by design.** `five`/`six`
  assert the full per-step trace; `four`/`three` assert the exact step count and
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
- Raw-`I64`-address **loads** are unimplemented (`check_load` /
  `find_state_load` `todo!()`), though stores are.
- Multi-element list slice get/set returns `ListMultiple` (unimplemented;
  `covers` is collected but never applied).
- `.ascii` parsing (`new_ascii`) is entirely `todo!()`; `#@`/section is unparsed.
- `wfi` is modeled as racy (over-approximation → some valid programs rejected,
  slower exploration); interrupt state is unmodeled.
- No emission of *linkable* RISC-V assembly, and no QEMU execution wiring (the
  motivating next step — see [README.md](README.md) and [language.md](language.md)).
- `partial`/`sequential`/`typed`/`racy-groups` compiler modes and the
  list/union exploration CLI args (`list_depth`, `list_width`, `union_depth`) in
  [language.md](language.md) are designed but not implemented.
