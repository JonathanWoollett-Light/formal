# Developing formal

This is the technical reference for working on `formal` itself: a precise
description of how the codebase is structured and how compilation and
verification actually work, plus the design intent behind it
([§11](#11-design-notes--roadmap)). It is written to be read by any
contributor, human or AI.

For _usage_ (installing the CLI, compiling and running your first program) see
[README.md](README.md); for how `formal` positions against other languages see
[comparison.md](comparison.md).

---

## 1. What this is

`formal` is a compiler/formal-verifier for an annotated dialect of RISC-V
assembly aimed at bare-metal RISC-V. Its distinguishing idea: a program is only
accepted if it can be **proven** correct across _every_ hart (hardware thread)
interleaving and _every_ admissible type/locality assignment of its
under-specified variables. "Correct" means **no `#!` ("fail") marker is
reachable** and every memory access is in bounds / permitted. The proof
additionally _infers_ each variable's type and locality and yields the
reachable-node / taken-branch sets that drive optimization.

The verifier is a symbolic interpreter over abstract (interval / tagged-pointer)
values, exploring an explicit execution tree.

A thin Python-like front-end (working name `hl`; the language itself is not yet
named) sits on top: [src/hl.rs](src/hl.rs) translates each `hl` statement to
exactly one dialect line ([§5.1](#51-the-hl-front-end)), so the dialect stays
the verifier's only input language.

### Current status (current at the time of writing; verify against the code)

- **Crate layout**: builds as a **library** (`src/lib.rs`, crate `formal`) plus
  a thin binary (`src/main.rs`). The library exposes the whole pipeline so the
  integration tests can call it.
- **Builds**: `cargo build` succeeds with no warnings.
- **Exploration is deterministic.** The same program + system configuration
  always produces the same step sequence, configuration and output (see the
  determinism note at the end of [§4.3](#43-verification--explorerer)).
- **`cargo test` passes.** The verifier is exercised through the integration
  tests in [tests/](tests/) (`uart_hello`/`racy_increment`/`racy_store_inferred`/`racy_store_annotated`/`heap_regions`), which translate
  each `input.hl` (pinning the exact stored `dialect.s`), then parse,
  verify and optimize the programs and assert the inferred
  `TypeConfiguration`, the **runtime-accessed byte ranges** (`accessed`, which drives
  dead-data elimination in codegen, [§4.8](#48-code-generation--emit_executable-srccodegenrs)),
  the optimized output, the exact emitted program, and the **exact incremental**
  behaviour of the state machine (a full per-step trace for `racy_store_inferred`/`racy_store_annotated`; the
  exact step count and type-inference timeline for `racy_increment`/`uart_hello`). `raw_access_undeclared` pins
  the every-access-must-verify rule (a raw access no `#@` region describes →
  `Invalid`). See [§6](#6-integration-tests-tests).
- **The binary is the `formal` CLI.** [src/main.rs](src/main.rs) is a small
  command-line tool: `formal new <name>` scaffolds a Rust project (`cargo new`
  plus the `formal` git dependency, a starter `main.hl`, and a build-script
  `src/main.rs`) whose `cargo run` compiles `main.hl` end to end. The whole
  pipeline is also exposed as one library call, `formal::compile`
  ([§4.9](#49-the-compile-api--the-formal-cli)).

So the working surface is the full pipeline: _hl::translate → parse → compress →
verify → optimize → emit_, reachable both through the integration tests and
through `formal::compile` / the generated project's `cargo run`.

## 2. Commands

`cargo build` is the **single setup entry point**: [build.rs](build.rs) detects
(and best-effort, non-interactively installs) the system dependencies the tests
and the distributed backend need (WSL on Windows, `qemu-system-riscv64`, the
RISC-V GNU toolchain, a system MPI library), reporting an exact command for
anything needing admin/reboot. It never fails the build and is idempotent;
control it with `FORMAL_NO_SETUP=1` (skip), `FORMAL_SETUP=detect` (report only),
or `FORMAL_SETUP=install` (install even under CI). See the README "Setup"
section.

```sh
cargo build           # compile lib + binary (and provision system deps via build.rs)
cargo run -- new foo  # the `formal` CLI: scaffold a project `foo` (see §4.9)
cargo nt              # run tests
cargo nt uart_hello   # run a specific test
cargo fmt             # formats the code
cargo clippy          # lints the code
cargo run --example translate -- tests/uart_hello/input.hl tests/uart_hello/dialect.s
                      # regenerate a test's stored dialect from its hl source
```

`cargo-nextest` is the preferred runner (install once with
`cargo install cargo-nextest`, or the prebuilt from https://get.nexte.st).

**Code coverage.** `cargo cov` runs the whole suite under LLVM source-based
coverage through that same nextest runner (the `cov` alias is
`llvm-cov nextest`). One-time setup: `rustup component add llvm-tools-preview`
and `cargo install cargo-llvm-cov`. `cargo cov --summary-only` prints per-file
region/line/function coverage; `cargo cov --html` writes a browsable report to
`target/llvm-cov/html`. Coverage instruments the Rust crate (the verifier, `hl`,
codegen, `explore`), not the QEMU/MPI subprocesses the boot/cluster tests shell
out to, so it measures the compiler's own line/branch coverage - a naive but
useful "is this code exercised at all" signal. Adding a behaviour to the verifier
should come with a test that covers it (e.g. `tests/reg_add` covers the `add`
instruction's lowering + symbolic semantics).

The aim is high coverage from **sensible programs and inputs**, not contrived
line-poking. The baseline is ~79% of regions (`lib.rs` ~97%, `hl.rs` ~89% via
`tests/compile_api` exercising `formal::compile` and `tests/translate_errors`
exercising the front-end's rejection paths; `main.rs` ~70% via `tests/cli`
running the binary). `src/draw.rs` (an unreferenced verifier-tree visualisation
helper with no public API) is excluded from the measurement - covering dead code
would mean tests that exist only to move the number. The largest remaining gap is
in `verifier_types.rs`/`verifier.rs`: those are mostly the **value/arithmetic
paths for type/operation combinations the language does not implement yet**. The
register-register arithmetic set (`add`/`sub`/`mul`/`div`/`rem`) and indexed
addressing have since landed (with the `reg_*`/`indexed` tests), so those paths
are now covered; what remains uncovered is the rarer combinations that still
`panic` on a `todo!` (unions, multi-element list slices, some width/sign mixes,
`.ascii`). They are deliberately uncovered until the feature lands, so coverage
of that code climbs **with** each new operation rather than from a test written
against an unimplemented path. Re-run `cargo cov` after adding a feature.

Tests print **nothing live to the console** (interactive output corrupts the
runner's display); long phases stream progress to
`target/tmp/test-logs/<test>/<phase>.progress` via the `Progress` helper in
`tests/common/mod.rs` (`Get-Content -Wait` to follow). Each test's `target/tmp`
output is grouped under its own `target/tmp/test-logs/<test>/` directory. The
parallel-emulation tests additionally stream a live **utilisation** breakdown to
`parallel-<n>nodes.progress` (the in-process pool) and `distributed-<n>nodes.progress`
(the distributed simulation), via `utilisation_log` + the
`verify_configuration_*_observed` entry points. One line per BFS wave, modelling a
cluster of nodes each with `cores_per_node` cores: the frontier width and, **per
node**, how many of its cores stepped a continuation that wave and at what percent
(`node0 8/8 (100%) | node1 6/8 (75%) | …`). Big counts are comma-grouped. Watch
utilisation climb as the frontier fans out and fall away in the tail. **`wsl.exe` must be
spawned detached from the console** (`CREATE_NO_WINDOW` in `run_in_qemu`): if
it attaches to the parent console it mutates the console mode and corrupts all
subsequent runner output in that window (staircased lines; progress bars
printing a new line per redraw). The repo also defines the alias `cargo nt` =
`nextest run` ([.cargo/config.toml](.cargo/config.toml)); with the WSL spawn
console-detached, nextest's live display renders correctly, and
`--show-progress none` remains available if a console still mis-renders (note
cargo's `[env]` table does **not** reach external subcommands, and the project
deliberately keeps configuration in repo files rather than machine-level config
_files_). The
test profile is **optimized with debug assertions kept on**
(`[profile.test] opt-level = 3` in [Cargo.toml](Cargo.toml)): the verifier
explores ~2M steps for `uart_hello`, while the internal `(0..N)` loop guards
and the `excluded`/`counter`/`hash`/`last_out` fields behind
`#[cfg(debug_assertions)]` remain active.

## 3. Repository layout

| Path                                           | Role                                                                                                                                                                                                                                                                                                                       |
| ---------------------------------------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| [src/lib.rs](src/lib.rs)                       | Library root: declares + re-exports the modules, and defines `compress` (node re-allocation) and `print_ast` (serialization).                                                                                                                                                                                              |
| [src/main.rs](src/main.rs)                     | The `formal` CLI: `formal new <name>` scaffolds a project whose `cargo run` compiles its `main.hl` ([§4.9](#49-the-compile-api--the-formal-cli)).                                                                                                                                                                          |
| [src/hl.rs](src/hl.rs)                         | The `hl` front-end: `translate` lowers the Python-like layer one statement to one dialect line ([§5.1](#51-the-hl-front-end)).                                                                                                                                                                                             |
| [examples/translate.rs](examples/translate.rs) | CLI over `hl::translate`; regenerates a test's `dialect.s` from its `input.hl`.                                                                                                                                                                                                                                            |
| [examples/compile.rs](examples/compile.rs)     | CLI over `formal::compile`; runs an `hl` file through the whole pipeline and prints the dialect + assembly (a scratch driver for developing `hl` programs).                                                                                                                                                                |
| [std/std.hl](std/std.hl)                       | The standard-library prelude (the `hl` dialect), prepended to every program by `translate`; defines `print` ([§5.1](#51-the-hl-front-end)).                                                                                                                                                                                |
| [src/ast.rs](src/ast.rs)                       | Lexer/parser front-end: `AstNode` intrusive list, `Instruction` enum, all operand types, per-instruction parsers and `Display` impls.                                                                                                                                                                                      |
| [src/verifier.rs](src/verifier.rs)             | The `Explorerer` state machine, the heart of verification.                                                                                                                                                                                                                                                                 |
| [src/verifier_types.rs](src/verifier_types.rs) | Symbolic value & memory model, `State`, `TypeConfiguration`, runtime type reflection. No `unsafe`.                                                                                                                                                                                                                         |
| [src/optimizer.rs](src/optimizer.rs)           | `remove_untouched` and `remove_branches` post-proof optimizations.                                                                                                                                                                                                                                                         |
| [src/codegen.rs](src/codegen.rs)               | `emit_executable`: lowers the verified+optimized AST + inferred layout into runnable RISC-V (generated `.data`/`.bss` + lowered directives).                                                                                                                                                                               |
| [src/draw.rs](src/draw.rs)                     | `draw_tree`: ASCII rendering of a `VerifierNode` tree (debug/diagnostic).                                                                                                                                                                                                                                                  |
| [tests/](tests/)                               | Integration tests, one folder per test (named after the behaviour it pins; see [§6](#6-integration-tests-tests)): `tests/<name>/main.rs` plus that test's assets (`input.hl`, `dialect.s`, stage pins). `common/mod.rs` holds the shared helpers. The Valid-outcome tests also lower their output and **boot it in QEMU**. |
| [scripts/build-run.sh](scripts/build-run.sh)   | Assemble + link (`as`/`ld`) the generated `target/gen/*.s` and boot in QEMU.                                                                                                                                                                                                                                               |
| [assets/](assets/)                             | Scratch inputs for the binary harness (`one.s`, `two.s`); the test programs live in their `tests/<name>/` folders.                                                                                                                                                                                                         |
| [comparison.md](comparison.md)                 | Positioning against Python/C/C++/Rust/Zig/Lean/Ada-SPARK.                                                                                                                                                                                                                                                                  |
| [index.html](index.html)                       | The marketing page (static, Pico.css; format with `npx prettier ./index.html --write`).                                                                                                                                                                                                                                    |

## 4. The compilation & verification pipeline (precise description)

The pipeline, as orchestrated in [src/main.rs](src/main.rs) and the tests, is:

```
hl::translate (front-end, §5.1)  →  new_ast (parse)  →  compress  →  Explorerer / next_step (verify)  →  remove_untouched / remove_branches (optimize)  →  print_ast (serialize) / emit_executable (codegen)
```

The first stage is pure text to text (the dialect is also accepted directly);
everything from `new_ast` on consumes the dialect.

### 4.1 Parsing: `new_ast` ([src/ast.rs:65](src/ast.rs#L65))

Input is the whole source as a `&[char]`. There is no separate tokenizer; the
parser matches raw `char`-slice patterns.

- The source is split into **lines** (one `AstNode` per non-empty line) by
  scanning for the platform newline: `\r\n` on Windows, `\n` on Linux (selected
  via `#[cfg(target_os = ...)]` at [src/ast.rs:75](src/ast.rs#L75)).
- Each line goes to `alloc_node` ([src/ast.rs:111](src/ast.rs#L111)), which:
  1. skips leading spaces; an all-space line produces **no node**;
  2. dispatches on the trimmed slice: `#!`→`Fail`, `#?`→`Unreachable`,
     `#$ …`→`Define(new_cast(..))`, `#& …`→`Lat(new_lat(..))`,
     `#@ …`→`Region(new_region(..))`, any other `#…`→a dropped comment (no
     node);
  3. otherwise strips any inline `# comment` and passes the code to
     `new_instruction` ([src/ast.rs:217](src/ast.rs#L217)), which matches the
     mnemonic prefix and calls the matching `new_*` constructor;
  4. heap-allocates the node with raw `alloc` + `write` + `NonNull` and links it
     onto the tail.
- Nodes form an **intrusive doubly-linked list** of `AstNode { prev, value, next }`
  ([src/ast.rs:7](src/ast.rs#L7)). `new_ast` returns the head
  (`Option<NonNull<AstNode>>`).

Per-instruction parsers extract operands by **hard-coded character offsets**
(e.g. `lhs = src[0..2]`, `rhs = src[4..6]`, third operand from index 8). This
assumes exactly 2-char register names and `", "` separators; see the parser
limitations in [§9](#9-conventions--gotchas).

### 4.2 Compression: `compress` ([src/lib.rs:21](src/lib.rs#L21))

Walks the linked list into a `Vec`, then re-allocates every node into a **fresh
per-node `Layout::new::<AstNode>()` allocation** (bitwise-moving it, re-linking
`prev`/`next`) and frees the originals, so the nodes are laid out back-to-back
after parsing for the many traversals the verifier performs. The head pointer is
updated in place. Purely a memory-layout pass; semantics are unchanged.

It must use the **same per-node allocation** as [`new_ast`], not one big
`Layout::array` arena: the optimizer (`remove_untouched` / `remove_branches`)
frees dead nodes one at a time with `Layout::new::<AstNode>()`, so freeing an
individual node out of an arena would be a bad-free (it was, once `*root` actually
pointed into the arena - see [§9](#9-conventions--gotchas)).

<a id="43-verification--explorerer"></a>

### 4.3 Verification: `Explorerer` ([src/verifier.rs:150](src/verifier.rs#L150))

The verifier is an **incremental state machine**. The caller repeatedly calls
`next_step(self) -> Result<ExplorePathResult, CompilerError>` (it consumes and
returns `self` by move inside `Continue`), each call advancing the exploration
by one AST node. It terminates as `Valid(ValidPathResult)`, `Invalid`, or an
`Err` for an unsupported construct / violated invariant (see §9's error model).

**The execution tree.** Exploration is recorded as a tree of raw-pointer nodes:

- `VerifierConfiguration` ([src/verifier.rs:65](src/verifier.rs#L65)): one per
  _system_ (an `InnerVerifierConfiguration { sections, harts }`). The root.
- `VerifierNode` ([src/verifier.rs:82](src/verifier.rs#L114)): one executed
  instruction step: `{ prev, root, hart, node: NonNull<AstNode>, next }`. `hart`
  is which hart executed it.
- `VerifierLeafNode` ([src/verifier.rs:99](src/verifier.rs#L131)): a frontier
  tip: `{ prev, variable_encounters: Map<Label, *VerifierNode>, hart_fronts: Map<hart, *VerifierNode> }`.
  `variable_encounters` records where each variable was _first_ seen on this
  path (used for backtracking); `hart_fronts` the most-recent node per hart.
- `InnerNextVerifierNode::{ Branch(Vec<*VerifierNode>), Leaf(*VerifierLeafNode) }`
  is the forward link.

State is **not** stored at interior nodes. Each _live leaf_ carries a cached
`State` (`Explorerer::state_cache`, the state before the leaf's `prev.node`
executes), and `queue_up` derives every successor leaf's state incrementally:
the parent's cached state plus **one** `apply_node` (the per-instruction
transfer function factored out of `find_state`). A step is therefore O(1) in
path depth. The replaying `find_state` (rebuild from the root, one `apply_node`
per path node) remains as the fallback after backtracking, which clears the
cache (the configuration changed and leaves were rebuilt); `state_for` rebuilds
lazily. Two details keep cached and replayed states identical: descriptor tag
allocation lives in `State::tag_index` (see `nth_tag`; the sequence is
path-determined either way), and `seed_label` seeds a variable's
storage/configuration entry when its `#$`/`la`/`#&` node is applied: the
global configuration gains variables mid-exploration, so a state cached before
an encounter can't have been seeded upfront the way `State::new` seeds replays.
The cache is keyed by leaf pointer but only ever probed per-leaf (never
iterated), so the pointer ordering is unobservable.

**Initialization** (`Explorerer::new`): requires every system has `harts > 0`,
then seeds each system (via `build_initial_chain`) with an initial chain of one
`VerifierNode` per hart (all pointing at `start_ptr`, **the first AST node**),
terminated by a `VerifierLeafNode` pushed onto `queue`. There is no `.global`/
`_start:` entry: verification (and execution) starts from the first line, like
Python (the runnable entry is added later by codegen). `configuration` starts
empty.

> Because the first instruction can itself be a variable's first encounter (its
> encounter node is then in the initial chain, with the root as predecessor),
> `invalid_path` detects `encounter.node == start_ptr` and, instead of walking
> back to a predecessor that doesn't exist, rebuilds the whole initial chain with
> `build_initial_chain`. (With an explicit `_start:` label this never happened:
> the label buffered the root from any encounter.)

**One step** (`next_step`, [src/verifier.rs:342](src/verifier.rs#L342)):

1. If `queue` is empty → **`Valid`**: every reachable path under the current
   `configuration` has been validated with no `#!` reached. Returns
   `ValidPathResult { configuration, touched, jumped, accessed, transitions,
uncompactable, pinned_nodes }`.
2. Pop (peek) the front leaf; mark its AST node in `touched`.
3. Dispatch on the instruction:
   - **No-op for checking** (`Li`, `Label`, `Addi`, `Blt`, `Csrr`, `Bne`,
     `Bnez`, `Beqz`, `Bge`, `Wfi`, `Beq`, `J`, `Unreachable`, `Region`):
     nothing to check here; their _effects_ are applied later by
     `find_state`/`queue_up`.
   - `Define` / `Lat` / `La`: `load_label(..)` (see
     [type inference & backtracking](#type-inference--backtracking) below).
     Failure → invalid.
   - `Sw`/`Sb` → `check_store`, `Ld`/`Lw`/`Lb` → `check_load`
     ([src/verifier.rs:847](src/verifier.rs#L847)/[822](src/verifier.rs#L992)):
     reconstruct `State`, read the destination register; if it is a tagged
     `Ptr`, bounds-check `type_size + ptr_offset + insn_offset <= size(type)`;
     if it is a raw `I64` address, find a covering `Section`, one configured on
     the system **or declared by an already-executed `#@`** (the replayed
     `state.memory.sections`), and check `Permissions`/`volatile`. The section
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

- `load_label` ([src/verifier.rs:719](src/verifier.rs#L719)): on first encounter
  of a label it builds an iterator `locality_list() × type_list()` (best→worst:
  localities `[Thread, Global]`; scalar types `[U8, I8, U16, I16, U32, I32, U64,
I64]`), restricted to any explicitly-annotated locality/type, picks the first
  candidate, inserts it into `configuration`, and pushes the label onto the
  `encountered` stack. If the label is already configured it instead _checks_
  the annotation matches (this catches conflicting `#$` defines), and, for a
  thread-local, records the encountering hart in the `Thread` hart set (each
  recorded hart gets its own `.bss` copy seeded by `State::new`; without this a
  second hart's access would find no memory behind its `MemoryLabel`).
- On any invalid path, `outer_invalid_path`
  ([src/verifier.rs:539](src/verifier.rs#L539)) pops the **most recently**
  encountered variable, calls `invalid_path` to deallocate the subtree from that
  variable's first-encounter node (rebuilding affected leaves), and tries the
  variable's _next_ `(locality, type)` candidate. If its iterator is exhausted,
  the variable is dropped and the next-most-recent variable is tried. If the
  `encountered` stack empties → **`Invalid`**: the program has no valid type
  configuration.
- List/union types are **never** explored automatically (infinitely many), so a
  list/union variable must be declared with `#$` (e.g. `#$ welcome _ [u8 u8]`).

**Hart interleaving enumeration** (`queue_up`,
[src/verifier.rs:1136](src/verifier.rs#L1136)). For each hart's current node a
`followup` closure classifies the next instruction as **racy** or **non-racy**.
The classifier (`compute_next`) is given the **post-front** state -- the current
node's own effect already applied -- because the lookahead for a load/store reads
its address register, which the current node may have just defined (an `la`);
classifying against the pre-front state would miss that definition. The arms:

- Loads/stores (`Sb`, `Sw`, `Ld`, `Lw`, `Lb`) are racy **iff** the pointer's
  `MemoryLabel` is `Global` (thread-local accesses assert `thart == hart` and
  are non-racy); raw `I64`-addressed accesses are racy; `Wfi` is treated as racy
  (conservative over-approximation, design note at
  [src/verifier.rs:145](src/verifier.rs#L145)); **`#@` (`Region`) is racy**: a
  region only becomes accessible once its declaration executes, so its order
  relative to other harts' raw accesses is observable and collapsing it would
  skip the (invalid) access-before-declaration interleavings; everything else
  is non-racy.
- Conditional branches are resolved _concretely_ from the symbolic register
  ranges using `compare`/`compare_scalar` (`RangeOrdering`/`RangeScalarOrdering`);
  `csrr … mhartid` is special-cased. This is the **symbolic hart-id model**: a
  `csrr mhartid` yields a symbolic `Csr(Mhartid)` value, not a concrete id, and a
  branch on it resolves only by `== 0` / `!= 0`, keyed on the internal hart
  index (index 0 reads 0; every other index is non-zero). So the verifier assumes
  only that **exactly one hart reads 0 and the ids are otherwise opaque** -- never
  that they are contiguous (`0,1,2`); the real hardware could hand out `[0, 15, 7]`.
  A program can therefore elect a single leader (`if mhartid == 0:`) but cannot
  use the id as a 0..N-1 rank. (See `fannkuch_v2`/`three_harts`.) A taken jump
  records the branch node in `jumped`.
- **Interleaving rule:** if _any_ hart's next step is non-racy, only that single
  deterministic node is queued (collapsing redundant interleavings; this is
  what bounds the `h^r` blow-up); only when _all_ harts' next steps are racy does
  the tree fork into one branch+leaf per hart, enqueuing every interleaving.

**Runtime-accessed byte ranges (dead-data analysis).** When a load/store node
is applied (`apply_node` → `find_state_load`/`find_state_store`), its
`(label, offset.start .. offset.stop + len)` is recorded straight into
`Explorerer.accessed` (an `AccessedRanges = BTreeMap<Label, BTreeSet<(u64,
u64)>>`) through the `RecordSinks` borrows threaded into state application,
using the full symbolic offset span so an under-determined access never
under-records. The `Lat` arm maps the generated descriptor tags (`_a`, …) to
the symbols codegen emits (`__<label>_type` / `__<label>_subtypes`) via
`State.descriptor_labels`, so descriptor reads are recorded under names codegen
can look up. The unions are idempotent (a post-backtrack `find_state` replay
re-records its whole prefix harmlessly) and, like `touched`, only ever grow
(entries from abandoned configurations remain): an **over-approximation**,
which is the sound direction for dead-data elimination. **States exclude the
instruction being processed** (a leaf's state precedes its node; the node is
applied only when successors are queued), so `check_store`/`check_load`
additionally record the _current_ instruction's own bytes (via
`record_access_into`) when its check passes. Without this, an access whose
successors all halt (`#?`) is never applied and its bytes would be wrongly
elided (pinned by the `terminal_access` test). Raw (`I64`-addressed) accesses
are _not_ recorded: they target heap/MMIO, not generated storage (soundness of
trimming therefore **assumes raw regions never alias generated storage**; see
§10). This bookkeeping must never feed back into exploration control flow.

Alongside `accessed`, the same sites record **pointer transitions**
(`Explorerer.transitions`, an `AccessTransitions = BTreeMap<NonNull<AstNode>,
BTreeSet<(Label, from, to)>>`): per AST node, which old byte offset a pointer
held before the instruction and which offset it produced (`addi`) or
dereferenced (loads/stores, `to = from + insn offset`). These drive the
instruction rewriting of **layout compaction** in codegen ([§4.8](#48-code-generation--emit_executable-srccodegenrs)).
A transition whose offsets are only known as a _range_ instead inserts the label
into `Explorerer.uncompactable`: no single rewritten immediate can re-point
it, so the region keeps the padded layout. And any **non-pointer execution** of
an `addi`/load/store node (a raw `I64` address, a scalar operand, or a range
offset) inserts the node into `Explorerer.pinned_nodes`: that execution is
invisible to the transition records, so the node must keep its _original_
immediate; compaction demotes any region that would require rewriting it
(pinned by the `mixed_pointer_raw` test, where one `sb` stores through a
pointer on one loop iteration and a raw `#@` address on the next). All are
recorded through the same `RecordSinks` as `accessed` (including the check-time
self-record for path-terminal accesses), and like `accessed` must never
influence exploration.

**Outputs.** A successful proof yields `ValidPathResult`
([src/verifier.rs:1770](src/verifier.rs#L1770)):
`configuration: TypeConfiguration` (inferred type+locality per variable),
`touched: BTreeSet<NonNull<AstNode>>` (every reachable node),
`jumped: BTreeSet<NonNull<AstNode>>` (branches that ever take their jump),
`accessed: AccessedRanges` (runtime-accessed bytes per region), and the layout
compaction inputs `transitions` / `uncompactable` / `pinned_nodes`; together
these drive dead-data elimination in codegen,
[§4.8](#48-code-generation--emit_executable-srccodegenrs).

`Explorerer` owns the whole tree and frees it in a manual `Drop`
([src/verifier.rs:1681](src/verifier.rs#L1681)).

**Determinism.** Exploration is deterministic: it must never let raw allocation
addresses influence control flow. The one place this was violated was
`invalid_path` ([src/verifier.rs:585](src/verifier.rs#L585)), which grouped
backtracked leaves in a `BTreeMap<*mut VerifierNode, _>`, ordered by pointer
value, so the order replacement leaves were re-queued (and thus the whole step
order and total count) varied run-to-run. It now uses an insertion-ordered `Vec`
keyed off the deterministic `queue` iteration. When adding code that iterates
over nodes/leaves, **order by stable keys** (queue position, hart, AST position,
`Label`), never by pointer (`BTreeSet`/`BTreeMap` over `*mut`/`NonNull` orders by
address). The `next_step` determinism hash
([src/verifier.rs:391](src/verifier.rs#L391)) exists to catch regressions here.
Note `touched`/`jumped` are `BTreeSet<NonNull<AstNode>>` (pointer-ordered) but
only ever queried with `.contains()` and iterated as the AST list, so their
ordering is never observed.

### 4.4 Symbolic value & memory model ([src/verifier_types.rs](src/verifier_types.rs))

This module has **no `unsafe`**. Despite the name,
`MemoryPtr`/`NonNullMemoryPtr` are domain value types, _not_
`std::ptr::NonNull`; the only real `NonNull<AstNode>`s here are the opaque
node keys in `AccessTransitions`/`pinned_nodes`, which are never dereferenced.

- **Scalars are inclusive integer ranges.** `MemoryValueI8/I16/I32/I64`,
  `MemoryValueU8/U16/U32/U64` each hold `{ start, stop }` (`start..=stop`),
  unified behind the `RangeType` trait
  ([src/verifier_types.rs:240](src/verifier_types.rs#L240)) which provides
  interval `add`/`sub`, `compare`, `exact()` (Some iff `start==stop`), `any()`
  (full type range, used for unknown memory), and native-endian byte slicing.
- **`MemoryValue`** ([src/verifier_types.rs:660](src/verifier_types.rs#L660)) is
  the universal symbolic value carried in registers and memory:
  scalars, `List(Vec<MemoryValue>)`, `Ptr(MemoryPtr)`, `Csr(CsrValue)`. `Add`
  implements pointer + scalar arithmetic.
- **Pointers are `(MemoryLabel, MemoryValueU64 offset)` pairs**, not addresses,
  so aliasing is reasoned about by _label identity_. `MemoryLabel`
  ([src/verifier_types.rs:1235](src/verifier_types.rs#L1235)) is
  `Global { label }` or `Thread { label, hart }`.
- **Memory** is `MemoryMap` ([src/verifier_types.rs:1259](src/verifier_types.rs#L1259)):
  a `BTreeMap<MemoryLabel, MemoryValue>` (`.bss`/`.data`) plus a `Vec` of raw
  `MemorySection`s with `Section` descriptors (system-configured + `#@`-declared).
  Reads/writes are byte-granular, addressed by `Slice { base, offset, len }`. A
  partial overwrite of a wide scalar **splits** it into a `List` of `U8` ranges
  with the written value spliced in (`MemoryValue::set`,
  [src/verifier_types.rs:870](src/verifier_types.rs#L870)). Raw `I64`-addressed
  stores resolve a `Section`, honour `volatile` (the store is dropped) and
  `permissions`. Non-volatile raw stores maintain a **backing** of
  `MemorySection`s serving two purposes: tracking stored _values_ (for future
  content assertions: raw _loads_ do not consult it yet; they return a
  full-range value of the loaded width in `find_state_load`) and tracking
  _which bytes are touched_. A store therefore always fills its **maximal
  span** `address.start .. address.stop + len`: backings overlapping the span
  are erased (absent backing reads as fully-unknown: the sound union of "old
  value or new value", allocation-free even for huge symbolic spans), then an
  exactly-addressed store whose value width matches `len` records the new
  bytes. Never silently drop a ranged store: that would leave stale "known"
  values behind.
- **Machine state** is `State { registers: Vec<RegisterValues>, memory,
configuration, descriptor_labels, tag_index }`
  ([src/verifier_types.rs:1554](src/verifier_types.rs#L1554)), one
  `RegisterValues` per hart. `State::new` seeds each configured variable with a
  full-range value (one `.bss` entry per hart for thread-locals).
  `descriptor_labels` maps generated descriptor tags to codegen's symbols and
  `tag_index` is the persistent tag counter (`nth_tag`); the dead-data
  _recording_ itself goes through the free functions
  `record_access_into`/`record_transition_into` straight into the `Explorerer`
  unions via `RecordSinks` ([§4.3](#43-verification--explorerer)).
- **`TypeConfiguration`** ([src/verifier_types.rs:1726](src/verifier_types.rs#L1726))
  = `BTreeMap<Label, (LabelLocality, Type)>`. `LabelLocality::Thread(BTreeSet<u8>)`
  records exactly which harts need a copy of a thread-local. `insert` enforces
  that all harts agree on a thread variable's `Type` and unions the hart set;
  `Global` labels must be unique.

### 4.5 Runtime type reflection: the `#&` / `lat` mechanism

`#& reg, label` loads a pointer to a **runtime type descriptor** that the
verified program can inspect (this is how the example programs check that
`welcome` is a `u8` list at runtime). `MemoryMap::set_type`
([src/verifier_types.rs:1398](src/verifier_types.rs#L1398)) lowers a (possibly
nested) `Type` into in-memory records. Each type becomes a **4-field list**:

```
[ u64 type-number, ptr-to-subtypes, u64 length, u8 locality ]
```

The _type-number_ is `FlatType as u64` ([src/ast.rs:279](src/ast.rs#L279)):
`U8=0, I8=1, U16=2, I16=3, U32=4, I32=5, U64=6, I64=7, List=8, Union=9`. This is
the `t2 = 8  # Load list type number` you see in
[tests/uart_hello/input.hl](tests/uart_hello/input.hl) (the `li t2, 8` of its
dialect form).
Nested lists are emitted as separate labelled records linked by `Ptr`; leaf
(non-list) types carry a null pointer and length 0. The schema of each record is
`memory_value_type_of()` = `List([U64, U64, U64, U8])`.

### 4.6 Optimization ([src/optimizer.rs](src/optimizer.rs))

Driven by the `ValidPathResult` sets, after a successful proof:

- `remove_untouched(ast, touched)` ([src/optimizer.rs:7](src/optimizer.rs#L7)):
  unlinks and `dealloc`s every node **not** in `touched` (dead-code elimination).
- `remove_branches(ast, jumped)` ([src/optimizer.rs:30](src/optimizer.rs#L30)):
  removes conditional branch instructions (`Bne`, `Blt`, `Beq`, `Beqz`, `Bnez`,
  `Bge`) **not** in `jumped` (a branch the verifier proved never jumps is dead).

Both rewrite the head pointer when the first node is removed.

<a id="47-serialization--print_ast-srclibrs65"></a>

### 4.7 Serialization: `print_ast` ([src/lib.rs:65](src/lib.rs#L65))

Walks the list and `Display`-formats each `Instruction`. The `Display` impls in
[src/ast.rs](src/ast.rs) define the **canonical text form**: registers print as
ABI names, immediates honour their stored radix (decimal or `0x`), loads print
`to, offset(from)`, stores print `from, offset(to)`, `#$`/`#&`/`#!`/`#?` print
their directive forms. On Windows it emits `\r\n`. This canonical form is what
the `uart_hello` test compares against [tests/uart_hello/ast.s](tests/uart_hello/ast.s); note
e.g. `(t0)` is normalized to `0(t0)`. `hl::translate` emits the same canonical
form (4-space indents, labels at column zero, explicit offsets, comments
dropped), so a generated `dialect.s` round-trips through parse + `print_ast`
unchanged.

<a id="48-code-generation--emit_executable-srccodegenrs"></a>

### 4.8 Code generation: `emit_executable` ([src/codegen.rs](src/codegen.rs))

Lowers the verified + optimized AST plus the inferred `TypeConfiguration` into a
**complete, runnable RISC-V program** (a `String`). This is the language's core
idea realized: the input leaves the memory layout implicit, the verifier infers
it, and codegen materializes it. It does **not** go through `print_ast` (which
emits the dialect verbatim for the test assertions); it walks the AST itself:

- Emits the `.global _start` / `_start:` entry the linker needs (the input has no
  explicit entry; execution begins at the first instruction, where verification
  began).
- Lowers the directives: `#$` (define) and `#@` (region) → kept as comments
  (both are compile-time metadata); `#& reg, label` (lat) → `la reg,
__<label>_type` (load the generated descriptor's address); `#!` (fail) →
  `ebreak`; `#?` (unreachable / end) → jump to a `__halt: wfi; j __halt` loop
  appended after `.text`.
- Emits `.data`: the runtime **type descriptors** read via `#&`, as records of
  `[u64 type-number, u64 subtypes-ptr, u64 length, u8 locality]` (the source
  layout §4.5 builds in `set_type`, 25 bytes/record), **minus the bytes the
  program never accesses at runtime** (next bullet).
- **Dead-data elimination & layout compaction.** `emit_executable` takes the
  proof's `accessed: AccessedRanges` + `transitions: AccessTransitions` +
  `uncompactable` and (in `solve_layouts`) builds a per-region `Layout`: the
  runtime-accessed bytes (field-granular for descriptors, since a `.dword`
  holding a relocation cannot be split; byte-granular for variables) and a mapping `f`
  from old offsets to emitted offsets. Unaccessed bytes are **removed**, and
  every instruction whose recorded transitions span a removed gap has its
  immediate rewritten to `f(to) - f(from)` during lowering (`patch_immediate`).
  A single immediate must satisfy _every_ recorded execution of its node; a
  fixpoint (iterated in AST order, deterministic) demotes the regions of any
  disagreeing node, or of a **pinned** node (one that also executed with a raw
  address/scalar operand, so it must keep its original immediate), or where the
  instruction has no rewritable immediate, or any region the verifier marked
  `uncompactable`, back to the **padded** layout: interior dead bytes below the last live byte become
  `.zero`, trailing dead bytes are dropped, immediates untouched. Concretely, in
  `uart_hello` `__welcome_type` emits 24 bytes and `__welcome_subtypes` **104**
  (13 type-number `.dword`s: each record's unread ptr/length/locality fields
  are gone, 325 padded bytes become 104) while the program's stride loop is
  rewritten `addi t0, t0, 25` → `addi t0, t0, 8`. Information only read at compile time does not exist in the
  output. _Caveat:_ compaction can move an access to a different alignment;
  QEMU `virt` emulates misaligned access, stricter hardware may need an
  alignment-preserving layout (future work).
- Emits `.bss`: zero-initialized storage for every inferred variable,
  compacted to its runtime-accessed bytes (a never-accessed variable emits just
  its label); regions with an under-determined access keep the full
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
CPU fault** (and that `uart_hello` writes `Hello World!` to the UART). The toolchain and QEMU
are **required**: the tests **fail** (not skip) if WSL / the toolchain / QEMU
are absent; point `RISCV_BIN` at the toolchain `bin/` (default
`$HOME/riscv-toolchain/riscv/bin`). [scripts/build-run.sh](scripts/build-run.sh)
does the same by hand from the generated files.

<a id="49-the-compile-api--the-formal-cli"></a>

### 4.9 The `compile` API and the `formal` CLI

The whole pipeline is exposed as one library call,
`formal::compile(source) -> Result<Compiled, CompileError>`
([src/lib.rs](src/lib.rs)): it runs `hl::translate` (with the std prelude),
parses, **verifies** (driving `Explorerer::next_step` to `Valid`), optimizes,
and lowers with `emit_executable`, returning `Compiled { combined, dialect,
assembly }` (the prelude-prepended source, the RISC-V dialect, the runnable
assembly). It verifies for **one hart with no `#@`/MMIO sections**, the config a
hosted program needs (the `print`/`exit` std reaches the outside through
`ecall`); bare-metal programs with regions or multiple harts need the
lower-level `Explorerer` directly (see §10). `compile` writes the dialect to a
temp file purely so `new_ast` spans (re-read from disk on error) resolve; like
the rest of the pipeline it leaks the AST (a one-shot is fine).

The **`formal` binary** ([src/main.rs](src/main.rs)) is a CLI over this.
`formal new <name>`:

1. runs `cargo new --bin <name>`;
2. appends the `formal` **git** dependency (not crates.io) to its `Cargo.toml`;
3. writes a starter [main.hl](std/std.hl) (the Python-dialect "Hello World!",
   `print` + `exit`) and a build-script `src/main.rs`;
4. ignores `build/`.

That generated `src/main.rs` _is_ the build: `cargo run` reads `main.hl`, calls
`formal::compile`, writes `build/main.hl` (the **combined** source: std prelude

- program), `build/main.dialect.s` (the dialect), and `build/main.s` (the
  runnable assembly), then assembles + links `build/main` (the RISC-V executable)
  with the RISC-V GNU toolchain it **downloads once into `build/toolchain`** (the
  latest `riscv64-elf-ubuntu-*-gcc` release from
  [riscv-collab/riscv-gnu-toolchain](https://github.com/riscv-collab/riscv-gnu-toolchain/releases)).
  The toolchain stages run **through WSL when present** (so it works on Windows),
  otherwise with `sh`. So every build artifact, including the toolchain, lives
  under `build/`. The website's "formal" comparison panel shows this flow
  (`formal new hello_world` → `cargo run` → count `build/main.s`).

## 5. The languages

<a id="51-the-hl-front-end"></a>

### 5.1 The `hl` front-end ([src/hl.rs](src/hl.rs))

A Python-like surface layer (working name `hl`; the language is not yet named)
that `translate(source: &str) -> Result<String, TranslateError>` lowers to the
dialect in [§5.2](#52-the-risc-v-dialect-as-actually-parsed). The design
constraint is that translation stays **trivially cheap and near-1:1**, the way
C maps near one-to-one onto assembly: every _simple_ statement lowers to
exactly one dialect line, and the three _structured_ statements (`if`, `while`,
`require`) each lower to a fixed pattern of one or two branches plus generated
labels. There is no register allocation, no implicit control flow beyond those
patterns, and no code synthesis. Control flow is **structured only**: there is
**no `goto` and no labels** in the surface language (both are rejected with an
error pointing at `if`/`while`); the labels in the dialect output are generated
(`_l0`, `_l1`, …). The simple statement forms:

| `hl` statement                           | Dialect line                                                                                                                                               |
| ---------------------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `value: global _` / `welcome: _ [u8]*13` | `#$ value global _` / `#$ welcome _ [u8 u8 … u8]` (a `name:` with an annotation is a define; `[t, t]` and `[t]*n` expand to the space-separated list type) |
| `t0 = &value`                            | `la t0, value`                                                                                                                                             |
| `t0 = type(welcome)`                     | `#& t0, welcome`                                                                                                                                           |
| `t0 = csr(mhartid)`                      | `csrr t0, mhartid`                                                                                                                                         |
| `t1 = 0x10000000`                        | `li t1, 0x10000000` (radix text preserved)                                                                                                                 |
| `t2 = t1`                                | `addi t2, t1, 0` (register move)                                                                                                                            |
| `t1 = t1 + 1` / `t1 = t1 - 8`            | `addi t1, t1, 1` / `addi t1, t1, -8` (immediate `+`/`-` only)                                                                                               |
| `t3 = t1 + t2` / `t3 = t1 - t2`          | `add t3, t1, t2` / `sub t3, t1, t2` (register-register)                                                                                                     |
| `t3 = t1 * t2` / `t3 = t1 / t2` / `t3 = t1 % t2` | `mul` / `div` / `rem t3, t1, t2` (register-register; `*`/`/`/`%` have no immediate form, so the operand must be a register)                          |
| `t0[0:4] = t1`                           | `sw t1, 0(t0)` (store; width 1 = `sb`, 4 = `sw`)                                                                                                           |
| `t1 = t0[8:16]`                          | `ld t1, 8(t0)` (load; width 1 = `lb`, 4 = `lw`, 8 = `ld`)                                                                                                  |
| `forget t0`                              | `#~ t0` (havoc: set `t0` to *any* value for the verifier; emits nothing)                                                                                    |
| `section 0x100 0x200 rw`                 | `#@ 0x100 0x200 rw`                                                                                                                                        |
| `fail` / `unreachable`                   | `#!` / `#?`                                                                                                                                                |
| `asm:` + indented lines                  | each block line emitted verbatim (the inline-assembly escape hatch; an empty block is an error)                                                            |

A **condition** is `<reg> <op> <reg>` with `<` / `<=` / `>` / `>=` / `==` /
`!=`, or `<reg> ==|!= 0`. `>` and `<=` swap the operands onto `blt`/`bge`; the
zero forms use `beqz`/`bnez`. The structured statements lower so the branch
**skips over** the block when the condition that should run it is false:

```text
require t1 < t2        ->      blt t1, t2, _l0      # branch over the fail when the require holds
                               #!
                           _l0:

if t0 == 0:            ->      bnez t0, _l1         # branch over the body when the condition fails
    <body>                     <body>
                           _l1:

while t5 != t2:        ->  _l2:                     # top-tested loop
    <body>                     beq t5, t2, _l3
                               <body>
                               j _l2
                           _l3:
```

`require <cond>` is exactly `if not <cond>: fail` in one line. Because the
branch guarding each `#!`/loop is taken on the _success_ path, a proven
`require`/`if` leaves an always-taken branch to the next line in the optimized
output (the verifier records it in `jumped`, so `remove_branches` keeps it):
the deliberate, accepted cost of dropping `goto`.

Loads and stores are byte slices off a register (`reg[offset : offset+len]`),
so the access width is visible at the call site. `#` starts a comment exactly
as in Python; comments and blank lines do not appear in the output. Output
formatting matches `print_ast`'s canonical form ([§4.7](#47-serialization--print_ast-srclibrs65)):
instructions/directives indented four spaces, labels at column zero, platform
line ending (`\r\n` on Windows, which the dialect parser requires there).
Errors are `TranslateError { line, message }` (1-based line; no panics).

**Indexed array access** is *not* a surface form; it falls out of the
register-register multiply and add as `base + i*elem`, then a slice. So
`arr[i] = v` (u32 elements) is written `t = i * 4; p = &arr + t; p[0:4] = v`
(see the `indexed` test). Keeping the 1:1 model means the cost (a `mul` + an
`add`) is visible, and a *concrete* index lowers to a concrete address (the
verifier's symbolic-index array writes are still unsupported, [§10](#10-known-limitations--todo-map)).

**`forget <reg>`** (`#~`) and **`assume:`** are the two verifier-only directives
for reasoning about a value the program reads at runtime. `forget t0` *havocs*
`t0` to the full range of its type, so the verifier proves the code for **every**
value (a sound over-approximation: the dual of `assume`); the runtime keeps
whatever `t0` already held. `assume:` + an indented block has the verifier
execute the block to **narrow** its symbolic state (e.g. `assume: n = 5` pins a
concrete value, making otherwise-unbounded loops determinate), while codegen
drops the whole block (it is bracketed `#(` / `#)`). `assume` is **unsound** by
construction (it asserts a fact the verifier does not check), the deliberate
escape hatch for making a runtime-`n` search tractable; `forget` then `assume`
is the idiom for "read `n` at runtime, prove a bounded proxy" (see the
`runtime_input`, `assume`, and `fannkuch_v1` tests). Both emit nothing.

**Compile-time type dispatch.** `if typeof <x> == <type>:` is resolved by the
**front-end**, not at runtime: it knows `x`'s category (an integer or register
is a scalar; a label names string/array storage) and the literal `<type>`
(parsed by the same type-expression parser `define` uses), compares them, and
either translates the body inline (no branch emitted) or skips it entirely.
Skipping is what lets one body carry arms for several argument types: the arm
that does not match is never translated, so e.g. a string arm's `&msg` is not
emitted (and cannot fail to translate) when `msg` is an integer. This is pure
monomorphisation -- no runtime type check, nothing leaks into the binary -- and
is what makes `print` polymorphic over `[u8]` (string) and `i64` (integer)
without a separate `print_int`.

`if`/`while` bodies are the **indented block** below the header (Python-style,
matched on indentation depth, no explicit terminator); `asm:` works the same
way. Dispatch order inside `statement` matters: assignment statements are
matched **before** the `name: <locality> <type>` define form because a slice
store like `t0[0:4] = t1` contains a `:` and would otherwise parse as a
definition.

[examples/translate.rs](examples/translate.rs) is the CLI
(`cargo run --example translate -- <input.hl> [output.s]`); each test pins
`translate(input.hl) == dialect.s` ([§6](#6-integration-tests-tests)), so the
stored dialect files are regenerated with it when the translator or an
`input.hl` changes.

**Functions and the standard library.** `def <name>(<param>):` + an indented
body declares an **inline** function (one parameter for now). There is no
calling convention, stack, or `ret`: a call `<name>(<arg>)` is expanded in
place, binding the parameter to the argument by whole-token substitution before
the body is translated afresh:

- a **string** argument `"literal"` is laid down in fresh thread-local storage
  (`__str0`, `__str1`, …: the `#$` define plus a `li`/`sb` per byte, NUL
  appended, so the verifier knows the exact contents) and the parameter binds
  to its label (`&param` in the body becomes `&__strN`, as `print` uses it);
- an **integer** argument binds the parameter to the literal value (`param` in
  the body becomes the number, as `exit` uses it);
- a **register** argument binds the parameter to that register (a scalar value,
  so the body's `if typeof param == i64` arm is taken), used to print a computed
  value, e.g. `print(a6)`.

The body is **hygienic**: any local definition in it (`name: <locality> …`) is
renamed to a fresh label per call (`__local0`, …, on a counter separate from the
branch labels so renaming never perturbs them), so two calls do not collide on
storage -- e.g. `print`'s integer scratch buffer, which two `print(int)`s would
otherwise both define.

A `def` itself emits **no** dialect lines: it is inert until called. The
translator prepends [std/std.hl](std/std.hl) (the `STD` constant,
`include_str!`'d) to **every** program; because its only contents are `def`s,
prepending it to a program that calls nothing from it leaves the lowering
byte-for-byte unchanged (this is why every existing test's `dialect.s` is
unaffected). User error line numbers stay 1-based (the prelude length is
subtracted). The library functions today are `print(msg)` and `exit(code)`
(end the process, syscall 93); both use `ecall`, so they target a hosted (Linux)
process, not bare metal. **`print` is polymorphic over its argument's type,
resolved at compile time** (see the `if typeof` dispatch above): `print("hi")`
lowers to a byte-walk + `write` (syscall 64); `print(42)` / `print(a6)` lower to
an integer formatter (peel decimal digits with `/`/`%`, write the slice). The
unmatched arm is never translated, so there is no runtime type check and no
separate `print_int`. See `linux_hello` / `print_poly` ([§6](#6-integration-tests-tests))
and the contrast with `uart_hello` (which pokes the QEMU UART with raw assembly).

<a id="52-the-risc-v-dialect-as-actually-parsed"></a>

### 5.2 The RISC-V dialect (as actually parsed)

- **Directives**: `#!` `Fail`, `#?` `Unreachable`, `#$ <label> <locality> <type>`
  `Define`, `#& <reg>, <label>` `Lat`, `#@ <start> <end> <perms>` `Region`
  (keyword `section`; declare an accessible memory region: bounds are immediates or registers,
  `end` exclusive, perms `r`/`w`/`rw`; executed in program order, so an
  allocator can declare each allocation as it makes it), `#~ <reg>` `Forget`
  (havoc a register to *any* value; verifier-only, codegen drops it), and
  `#(` / `#)` `Assume` (bracket a block the verifier executes to narrow state and
  codegen drops; the `assume:` escape hatch). Plain `#…` comments and inline
  `# …` comments are stripped.
- **Instructions** (`Instruction` enum, [src/ast.rs:260](src/ast.rs#L260), 34
  variants): `csrr`, `bnez`, `j`, `wfi`, `ecall`, labels (`foo:`), `.global`,
  `.data`, `.ascii` (parser is `todo!()`), `la`, `li`, `sw`, `lw`, `addi`,
  `add`, `sub`, `mul`, `div`, `rem` (register-register RV64M arithmetic),
  `amoadd.w rd, rs2, (rs1)` (RV64A atomic fetch-add, the lock-free
  work-claiming primitive: `rd = mem[rs1]; mem[rs1] += rs2` in one racy step),
  `blt`, `lb`, `beqz`, `sb`, `bge`, `ld`, `bne`, `beq`, plus the directives
  above. There is no `amoadd.w` surface form; it is written in an `asm:` block
  and parsed back from the emitted dialect (so the verifier models it, rather
  than treating the `asm:` block as opaque). `ecall` is the boundary to the host/OS: the verifier does not model
  its effect (it is a no-op for checking, non-racy, no state change) and
  codegen emits it verbatim, so the syscall ABI lives entirely in the registers
  the surrounding code sets (the std `print`'s `write`, and a program's `exit`).
- **Registers** (`new_register`, [src/ast.rs:1182](src/ast.rs#L1182)): **only**
  `t0`–`t5` and `a0`–`a7` are parseable (the `a2`–`a7` added for the system-call
  ABI), despite the full `X0`–`X31` enum existing for `Display`. Other register
  names cause `.unwrap()` panics at call sites.
- **CSRs**: only `mhartid`.
- **Types**: scalars `u8/i8/u16/i16/u32/i32/u64/i64`, `List` `[t t …]`, `Union`
  `{t t …}`.
- **Localities**: `global`, `thread` (and `_` = infer).

## 6. Integration tests ([tests/](tests/))

The tests are **integration tests** (one binary per test, in
`tests/<name>/main.rs`), so they can only use the crate's public API: this is
why the pipeline lives in the library and everything the tests need is `pub` /
re-exported at the crate root.

**Each test owns a folder** holding its sources and expectations side by side:

- `input.hl`: the Python-like source (comments allowed; they are dropped by
  translation).
- `dialect.s`: the stored dialect, **pinned** as `hl::translate(input.hl)`'s
  exact output by every test (the front-end analogue of pinning the emitted
  RISC-V at the other end of the pipeline). Generated, never hand-edited:
  regenerate with `cargo run --example translate -- tests/<name>/input.hl
tests/<name>/dialect.s` when the translator or the `input.hl` changes.
- Stage pins where the test asserts them, loaded with `include_str!` and
  compared through `normalize`: `ast.s` (canonical parse round-trip),
  `untouched.s` / `optimized.s` (after each optimizer pass), `emitted.s` (the
  exact generated program). Stored as **files**, not inline strings, so they
  get assembly syntax highlighting.

(`region_permissions` pins two programs, so its folder holds
`read_only.hl`/`read_only.s` and `write_only.hl`/`write_only.s` instead of the
`input.hl`/`dialect.s` pair.)

`tests/common/mod.rs` (included by each test via `#[path = "../common/mod.rs"]
mod common;`) holds the shared helpers:

- `setup_test(asset) -> Option<NonNull<AstNode>>`: reads `tests/<asset>`
  (e.g. `"uart_hello/dialect.s"`, resolved against `CARGO_MANIFEST_DIR`) and
  runs `new_ast` + `compress`.
- `trace_valid_path(explorerer) -> (Vec<String>, Result<ExplorePathResult, CompilerError>)`:
  steps the verifier to a terminal state, returning one **exact trace line per
  step** (see below) plus the terminal outcome: `Ok` of the terminal
  `ExplorePathResult` (`Valid`/`Invalid`), or `Err` of the [`CompilerError`] the
  verifier hit. The trace is returned in **all** cases (including error), with the
  failing step appended as the last line, so a test can show _where_ it stopped.
- `expect_valid(trace, result) -> ValidPathResult`: asserts `Ok(Valid(_))`,
  else panics with the outcome and the tail of the trace.
- `front_step(explorerer)`: reads the front queue leaf to report the
  `(hart, harts, instruction)` the next step will process.
- `config_timeline(trace)`: the sequence of distinct, consecutive `configuration`
  strings: i.e. the type-inference timeline (a reset to `Config: []` marks a
  backtrack).
- `assert_trace(actual, expected)`: compares a trace line-for-line, reporting
  the first diverging step index.
- `normalize(s)`: collapses `\r\n` → `\n` so the `\n`-based expected strings
  compare regardless of the platform line ending `print_ast` (and
  `hl::translate`) emits.
- `blessing()` / `bless_asm(rel, actual, included)`: re-baseline mode. With
  `BLESS` set in the environment, `bless_asm` **overwrites** the golden
  `tests/<rel>` with `actual` instead of asserting, `trace_valid_path` dumps
  the trace + step count to `target/tmp/test-logs/<test>/trace` and `.../meta`,
  and a test skips its inline trace / step-count assertions (guarded
  `if !blessing()`).
  One `BLESS=1` run therefore regenerates every golden **and still boots each
  program in QEMU** (so a blessed program is still proven to run); then paste
  the dumped trace / count back into the test source. Re-baseline
  **deliberately** (re-derive from new behaviour), never to mask a regression.
- `run_program(name, ast, configuration, accessed, transitions, uncompactable,
pinned_nodes)` / `run_in_qemu(name, asm)`:
  lower the optimized program with `emit_executable`, assert **no
  compile-time-only data leaked** (no `.byte` locality directives survive in the
  generated `.data`/`.bss`; none of these programs read locality at runtime),
  then assemble + link + **boot it in QEMU under WSL**, asserting no CPU fault
  and returning the captured UART output. The toolchain + QEMU are **required**:
  these panic (fail the test) if WSL / the toolchain / QEMU are missing (see §4.8).
- `run_linux(name, asm)`: the **hosted** counterpart, for `linux_hello`. Builds
  a **static ELF** (entry `_start`, no fixed text address) and runs it under the
  user-mode emulator `qemu-riscv64` (bundled in the toolchain `bin/`, invoked as
  `$RISCV_BIN/qemu-riscv64`), returning its **stdout**. Same required-not-skipped
  policy as `run_in_qemu`.
- `verify_with_model(asset, harts, model) -> ModelOutcome`: verifies a program
  under a chosen [`Model`] - `Sequential` (in-process [`verify_inferred`]) or
  `Hpc { ranks }` (distributed under `mpirun`, via `mpirun_formal`) - and returns
  the inferred configuration + accessed ranges as comparable strings, so one test
  body covers both. The model is **switchable before running** without an edit:
  `FORMAL_TEST_MODEL=sequential | hpc | hpc:<ranks>`. Each run writes a detail log
  under `target/tmp/test-logs/<test>/` (`sequential.log`, or `hpc.log` with the
  per-rank live progress + utilisation breakdown from `formal mpi-verify`).
  `mpirun_formal(ranks, args)` builds `--features hpc` in WSL (cached in
  `~/formal-hpc`) and runs `formal <args>` under `mpirun`; required-not-skipped
  like `run_in_qemu`. `tests/hpc_demo` is the worked example (`cargo nt hpc_demo`):
  a self-contained directory whose large racy program (`input.hl` → `dialect.s`)
  it verifies both in-process (lower + boot, pinning `emitted.s`) and under the HPC
  model, checking the distributed result equals the in-process one.

A trace line is `h<hart>/<harts> | <instruction> | <config> | q<n> t<n> j<n>`
(the instruction being processed this step, and the resulting configuration /
queue / touched / jumped state).

Each test first asserts the **translation pin**
(`normalize(hl::translate(include_str!("input.hl"))) ==
normalize(include_str!("dialect.s"))`), then verifies via `trace_valid_path`,
asserts the inferred `configuration` and the `accessed` byte ranges, runs
`remove_untouched` / `remove_branches`, asserts `normalize(print_ast(ast))`
after each, asserts the **exact emitted program** (`emit_executable`), and
finally `run_program`s the result (boots it in QEMU). The **incremental**
assertions differ by test:

- `racy_store_inferred`: racy store of `0` to `value` (type `_`, inferred), asserting
  `value == 0` with `require` (lowered to `beq …, _l0` over the `#!`). Asserts the **full
  95-step trace** (`assert_trace`): the type search `Gu8 → Gi8 → Gu16 → Gi16 →
Gu32` (config resets to `[]` at each failing `sw`), then the 2-hart racy
  interleavings fanning the queue out to 7 and draining to 0; the always-taken
  `beq` drives `jumped` to 1.
- `racy_store_annotated`: same program as `racy_store_inferred` but with explicit `#$ value global u32`, so the
  annotation is _checked_, never searched. Asserts the **full 67-step trace**.
- `racy_increment`: racy increment of `value` (type `_`); its interleaving fan-out is 744
  steps (too many to assert line-for-line, so `racy_store_inferred`/`racy_store_annotated` pin the per-step
  shape). Asserts the exact step **count**, the `config_timeline`
  (`Gu8 → … → Gu32`) and the optimized output.
- `uart_hello`: full UART "Hello World!" with list-type checking; 2111465
  steps (the racy UART writes interleave against the second hart; this is
  the test that motivated the per-leaf state cache). Asserts the AST round-trips to
  [tests/uart_hello/ast.s](tests/uart_hello/ast.s), the exact step **count**,
  the `config_timeline` (value search, then `welcome`'s 13-element `[u8 …]`
  joins),
  `{ value: (Global, U32), welcome: (Thread({0}), List([U8; 13])) }`, the exact
  `accessed` ranges (descriptor reads at offsets 0/8/16 of `__welcome_type` and
  each record's type-number at the 25-byte stride of `__welcome_subtypes`,
  never a locality byte), the **exact generated program** including the
  compacted `.data` (24-byte `__welcome_type`, **104-byte**
  `__welcome_subtypes`, no `.zero` padding, no `.byte` anywhere) and the
  rewritten stride (`addi t0, t0, 8`), and that QEMU's UART receives the full
  `Hello World!`.
- `linux_hello` ([tests/linux_hello/](tests/linux_hello/)): the **hosted**
  counterpart of `uart_hello`. The two-line source `print("Hello World!\n")` +
  `exit(0)` uses only the std library (`print` = the `write` syscall, `exit` =
  the `exit` syscall, both via `ecall`); the test verifies it (1 hart, no
  sections: the std reaches the outside through `ecall`, not a raw store), pins
  the exact emitted program, and via `run_linux` builds a **static ELF** and
  runs it under `qemu-riscv64`, asserting stdout is `Hello World!`. Pins that
  `print`/`exit`, `ecall`, and the `a2`/`a7` syscall registers work end to end.
- `fannkuch_redux` ([tests/fannkuch_redux/](tests/fannkuch_redux/)): the
  Benchmarks-Game fannkuch-redux (generate all n! permutations, count pancake
  flips, track max flips + the alternating checksum) for n = 5, the first
  **real algorithm** written in the dialect. It predates the dialect's multiply,
  register-register arithmetic, and indexed addressing (all added later), so
  every array access is a pointer walk and every reg+reg combine a `+/-1` loop,
  yet the whole thing lowers to ~120 instructions over three `[u32]*5` thread
  arrays. The distinguishing part: the two closing `require`s assert
  `max flips == 7` and `checksum == 11` (the known fannkuch(5) answer), so the
  proof's `Valid` outcome **is** a compile-time proof the algorithm is correct;
  the program then lowers to a static ELF and **runs under `qemu-riscv64`**,
  computing and exiting 0 with no output (the answer was already proven). This
  test motivated the integer-arm extensions to the value model (see
  [§9](#9-conventions--gotchas)).
- `reg_add` / `reg_sub` / `reg_mul` / `reg_div` / `reg_rem`
  ([tests/](tests/)): one per register-register arithmetic op, each computing a
  value (e.g. `5! = 120`, `100/7/3 = 4`) and proving it with a closing `require`,
  then booting under `qemu-riscv64`. Cover the `add`/`sub`/`mul`/`div`/`rem`
  lowering, the verifier's interval arithmetic, and codegen end to end.
- `indexed` ([tests/indexed/](tests/indexed/)): computed-index array access
  (`arr[i]` as `&arr + i*4`, then a slice) -- the point of adding multiply +
  register-register add; writes/reads `arr[1]` and `arr[3]` at computed addresses
  and proves their sum.
- `int_output` ([tests/int_output/](tests/int_output/)): integer printing by
  digit extraction (`/10`/`%10` into a buffer, ASCII, `write`); prints `42`.
- `print_poly` ([tests/print_poly/](tests/print_poly/)): the **polymorphic
  `print`** -- `print("Hi ")` + `print(42)` + `print(7)` -> `Hi 427`, the string
  arm and the integer arm of one `print` selected by the compile-time `if typeof`
  dispatch (and two integer prints exercising body-local-label hygiene). Asserts
  no directive leaks into the binary.
- `runtime_input` ([tests/runtime_input/](tests/runtime_input/)): a value the
  verifier cannot see, via `forget` -- it proves `arr[a0 % 4]` in bounds for
  *every* `a0` while the runtime keeps `a0 = 12`.
- `assume` ([tests/assume/](tests/assume/)): the `forget` + `assume:` idiom --
  `forget a0` havocs the value, `assume: a0 = 5` narrows it for a bounded proof;
  neither directive appears in the binary.
- `fannkuch_v1` ([tests/fannkuch_v1/](tests/fannkuch_v1/)): **V1** of the
  fannkuch split -- single-threaded, the input `n` read at runtime with the
  verifier blind to it (`forget`) and narrowed to 5 for a bounded proof
  (`assume`), arrays sized for the maximum n, the checksum + max flip count
  printed with the polymorphic `print`. Boots and prints `11\nPfannkuchen(5) = 7`.
- `three_harts` ([tests/three_harts/](tests/three_harts/)): a fast minimal
  3-hart smoke test. A leader/worker program (`if mhartid == 0:` gates the
  leader; others skip to a shared inline-asm `wfi`) verifies under a 3-hart
  configuration. No shared memory, so the harts are independent (non-racy) and
  the interleaving collapses -- it verifies in milliseconds.
- `fannkuch_v2` ([tests/fannkuch_v2/](tests/fannkuch_v2/)): **V2** of the
  fannkuch split -- multi-threaded (3 harts) + inline assembly, bare metal. All
  three harts read `mhartid`; the symbolic hart-id model guarantees only that
  exactly one reads 0 and the ids are unique (they could be `[0, 15, 7]`), so the
  program uses the one distinction the verifier can make -- `mhartid == 0` -- to
  gate the leader's work, while the others skip to a shared `wfi`. The leader
  reads `n` at runtime (`forget`+`assume`), computes fannkuch(n), and writes the
  result to the QEMU virt UART (0x10000000) as decimal -- bare metal, no `ecall`.
  Boots under QEMU; the UART receives `2\n2` (fannkuch(3)). `n` is kept small
  because the leader runs a long solo stretch while the workers sit parked far
  back -- the O(N^2) worst case for the front-search (see [§9](#9-conventions--gotchas)).
- `atomic_add` ([tests/atomic_add/](tests/atomic_add/)): `amoadd.w` end to end --
  an inline-asm atomic parsed back from the `asm:` block and modeled as a
  read-modify-write; proven (old value returned, counter incremented) and booted.
- `global_zero_init` ([tests/global_zero_init/](tests/global_zero_init/)): reads
  an **unwritten global** and proves it is 0. Globals live in `.bss` (zero at
  boot: the hosted loader zeroes it, and QEMU's ELF loader zeroes the NOBITS span
  of a bare-metal image), so the verifier models a global's initial value as 0
  (`zero_value` in `State::new`/`seed_label`). This is what lets a hart read a
  shared counter before any write -- lock-free work claiming with no start barrier.
- `atomic_claim` ([tests/atomic_claim/](tests/atomic_claim/)): two harts atomically
  fetch-add a zero-init global counter to each claim a unique rank; proven in
  range across every interleaving (the racy atomic on top of zero-init globals).
- `parallel_probe` ([tests/parallel_probe/](tests/parallel_probe/)): the full
  lock-free work-sharing pattern across **2 harts**, end to end -- claim a rank,
  do per-hart work, write a slot, and the last finisher (found by the atomic's
  return value, no spin) combines the slots and writes the total to the UART. The
  verifier proves it across every interleaving; QEMU boots two harts
  (`run_program_smp` -> `-smp 2`) and the UART gets `3`. (Three harts is not yet
  feasible: the racy interleaving x front-search cost exceeds the 10M-step bound.)
- `heap_regions` ([tests/heap_regions/](tests/heap_regions/)): `#@` region declarations
  (immediate bounds accessed at a non-zero offset, and register bounds exactly
  as wide as the store that hits them; the latter would panic in
  `MemoryMap::set` if it re-checked with the value's width instead of the
  instruction's) with racy raw stores/loads inside them; 1021 steps (`#@` is
  racy, so its interleavings against the accesses are explored). Asserts the
  round-trip (including both `#@` forms), empty `configuration`/`accessed`, the
  exact emitted program (no `.data`/`.bss` at all), and boots it in QEMU.
- `raw_access_undeclared`: loads from a raw address no `#@`
  region or section describes. Asserts the exact 2-step prefix trace and that
  the terminal outcome is **`Invalid`**: every memory access must be verifiable
  as safe.
- `region_overrun`: a 4-byte store into a 2-byte `#@`
  region. Asserts the exact 3-step prefix trace and the **`Invalid`** outcome,
  pinning the _direction_ of the section bounds check (`required_size <=
s.size`; with the operands swapped this would wrongly verify).
- `terminal_access`: a descriptor load whose only successor
  is `#?` (a path-terminal access, never interior to any replay). Asserts the
  full 4-step trace, that `accessed` still contains the load's bytes (the
  check-time record in `check_load`; without it dead-data elimination would
  emit a descriptor the program reads but that has no bytes), the exact emitted
  program (`__value_type` keeps its 8 live bytes, drops the other 17), and
  boots it in QEMU.
- `unsupported_construct`: a `.global` directive (via its `asm:` block), which
  the verifier does not model (programs have no explicit entry). Asserts that
  `trace_valid_path` returns `Err(CompilerError::Unsupported(_))` (rather than
  panicking) **and** that the trace's last line is the failing step: the
  error-path analogue of the success tests.

Behaviour-focused tests (each pins one specific rule or error case; the Valid
ones also pin the exact emitted program, and all Invalid ones pin their trace
prefix):

- `vague_access`: `record_access` with a _range_ offset fills the maximal span
  (a 4-byte store at offset `0..=6` records `(0, 10)`), and a recorded range
  that only partially overlaps a descriptor field emits the **whole** field
  (no sub-field elision) under the padded (`uncompactable`) layout: the
  soundness contract of dead-data elimination, and the only remaining pin of
  the `.zero`-padding fallback.
- `mixed_pointer_raw`: one `sb` node stores through a `value` pointer on
  iteration 1 and a raw `#@` address on iteration 2; the raw execution pins the
  node, so despite `value` having a single accessed byte the emitted program
  keeps `sb t3, 4(t1)` and full-size storage (compaction backs off rather than
  silently re-point the raw store). The two iterations are a `while` loop. 68
  steps; boots.
- `partial_variable_access`: accesses only bytes 0 and 2 of a `[u8 u8 u8 u8]`;
  `accessed` records exactly `(0,1)`/`(2,3)` and `.bss` compacts to those two
  bytes, the byte-2 access re-pointed to offset 1. 14 steps; boots.
- `descriptor_read_union`: hart 0 reads a descriptor's type-number, hart 1 its
  length; `accessed` is the union, so both fields are emitted (back to back:
  the unread field between them is removed and the length read re-pointed
  16 → 8) plus an empty subtypes array. The two reads are exclusive `if`
  blocks (`if t0 == 0:` / `if t0 != 0:`). 46 steps; boots.
- `locality_runtime_read` (the inverse of the elision rule): `lb` of the
  locality byte (offset 24) at runtime keeps the `.byte 1`; as the _only_
  emitted descriptor byte, the read re-pointed to offset 0 (bypasses
  `run_program`'s no-`.byte` assert). Boots.
- `offset_widened_inference`: a 4-byte store at offset 2 forces the type
  search through `u8…i32` to `u64` (the offset participates in inference);
  `accessed` is exactly `(2, 6)`. 29 steps; boots.
- `conflicting_defines` / `annotated_store_overflow`: contradictory `#$`
  defines / a `sw` into an annotated `u8`: annotated searches have one
  candidate, so backtracking exhausts → **`Invalid`**.
- `region_permissions` (two programs: `read_only.*`/`write_only.*`):
  store into an `r` region / load from a `w` region → **`Invalid`**.
- `region_declared_late`: the store precedes its `#@` in program order;
  regions take effect when executed (declare-before-use) → **`Invalid`**.

Because exploration is deterministic (see the determinism note in
[§4.3](#43-verification--explorerer)), the step counts and full traces are stable
contracts: re-derive them when behaviour legitimately changes; do not loosen
them to absorb a regression.

`two.rs` (obsolete API, ended in `todo!()`) and the old `src/tests/` unit-test
module have been **deleted**.

## 7. Verification complexity

Worst case `O(n · h^r · 2^b · 8^v)` where `n` = instructions, `h` = harts,
`r` = racy instructions, `b` = indeterminate branches, `v` = unspecified
variables. The non-racy interleaving collapse (`queue_up`) and chronological
type backtracking are the mechanisms that keep real programs far under this
bound. `8` is the count of scalar types in `type_list()`; `2` reflects branch
outcomes; `h^r` the racy interleavings.

Worked intuition: 10,000 instructions × 3 harts × 100 racy instructions × 100
indeterminate branches ≈ 6.5·10⁸¹: impossible. The same program with 10 racy
instructions (e.g. atomics managing shared state) and 10 indeterminate branches
≈ 6·10¹¹: feasible. The design lever is always _reducing the exponents_, not
the base: keep shared mutation rare, keep branches determinate, annotate types
(`uart_hello` at 13 racy UART writes × 2 harts is already ~2·10⁶ steps).

Planned (unimplemented) scaling modes trade soundness or precision for those
exponents; see [§11](#11-design-notes--roadmap).

### 7.1 Parallel decoupling

The cost has two independent axes that the original `Explorerer` fused into one
sequential loop via a global `configuration` plus chronological backtracking:

- **Outer**: the type/locality configuration search (`8^v · 2^v`).
- **Inner**: hart interleavings (`h^r`) and the branch tree (`2^b`) for a
  *fixed* configuration.

Once a configuration is fixed the inner search never backtracks (a `#!` or a
failed check is simply *Invalid for this configuration*), so it is an independent
subproblem: the unit that parallelises across cores and cluster nodes. This
decoupling is implemented (in [`src/explore.rs`](src/explore.rs), over the
sequential `Explorerer` which stays as the reference oracle):

- **Pointer-free addressing.** [`AstNodeId`](src/ast.rs) (a program-order index)
  and the [`Ast`](src/ast.rs) view replace `NonNull<AstNode>` as the stable key
  for a serialisable frontier item, honouring the §4.3 determinism rule. (This
  also surfaced a latent [`compress`](src/lib.rs) bug: it had left `*root` on the
  pre-compaction nodes, so making the relayout take effect exposed that its single
  `Layout::array` arena was incompatible with the optimizer's per-node frees;
  `compress` now re-allocates per node - see [§4.2](#42-compression-compress).)
- **Pointer-free primitives.** `apply_node` / `check_store_at` / `check_load_at`
  operate on `(state, hart, node, sinks)`, not the `*mut` tree (the old methods
  are thin wrappers); `compute_next` is the interleaving classification lifted
  out of `queue_up` (which now calls it).
- **`step` + fixed-config searches.** A pointer-free `step(Continuation)` (the
  analogue of one `next_step`+`queue_up`) drives three equivalent searches over a
  single seeded configuration: `verify_configuration` (reuses the `Explorerer`
  verbatim), `verify_configuration_pooled` (a `step` worklist), and
  `verify_configuration_parallel` (the worklist stepped across a **rayon** pool,
  the answer to "one configuration must still use many cores"). The
  [`Continuation`](src/verifier.rs) is `Send` and `serde`-serialisable.
- **Outer sweep + generator.** `verify_sweep` verifies candidate configurations
  concurrently and selects the lowest-rank valid one; `candidate_configs` +
  `verify_inferred` enumerate the candidates (`locality_list × type_list`) so the
  caller supplies only the AST and systems.
- **Distributed transport (simulated).** `verify_configuration_distributed_sim`
  runs the parallel inner search with every continuation crossing a `postcard`
  serialize/deserialize round-trip, exactly as it would migrating between nodes;
  the union reduce is unchanged. A pure-Rust cluster stand-in, in the normal
  test suite.
- **Distributed backend (real MPI, `--features hpc`, [`src/dist.rs`](src/dist.rs)).**
  Both axes run over rsmpi across `mpirun -n N` processes:
    - *Outer* (`outer_sweep_winner`): each rank verifies its share of candidate
      configurations; an MPI all-reduce(min) selects the lowest-rank valid one
      (only a `u64` crosses).
    - *Inner* (`verify_configuration_mpi`): one fixed configuration's frontier is
      distributed across ranks - each rank steps the continuations it owns, the
      successors are MPI all-gathered (so a continuation produced on one rank
      *migrates* to whichever rank owns its slot next - the real `postcard` bytes
      a node ships), and the per-rank `LocalAccumulators` reduce by commutative
      union. `all_gather_bytes` is the var-count all-gather both use.

  `formal mpi-selftest` runs both axes end to end. Building needs a system MPI +
  libclang (provisioned by `build.rs` under `--features hpc`), so it builds/runs
  on Linux / under WSL (see [`deploy/`](deploy/) for the k8s + Kubeflow MPI
  Operator target). The remaining work is purely a *scheduling* upgrade -
  replacing the per-wave barrier with lifeline work-stealing + Mattern
  termination detection for better load balance at scale; the transport and the
  reduce are done.

**How a verification executes** - the same exploration, exposed through five
backends that all produce the identical outputs:

| Backend | Entry point | Parallelism |
| --- | --- | --- |
| Sequential oracle | `Explorerer::next_step` | none (the reference) |
| Fixed-config | `verify_configuration` / `verify_configuration_pooled` | none |
| In-process pool | `verify_configuration_parallel` / `verify_sweep` / `verify_inferred` | rayon (all cores) |
| Distributed simulation | `verify_configuration_distributed_sim` | rayon + per-continuation serialize round-trip |
| Real MPI, wave | `outer_sweep_winner` + `verify_configuration_mpi` | `mpirun -n N`, barrier per wave |
| Real MPI, work-stealing | `verify_configuration_mpi_stealing` | `mpirun -n N`, barrier-free + load-balanced |

The flow is the same in every backend: seed one `Continuation` per system at the
program entry; `step` each frontier item (validate the active node, `apply_node`
it, classify the next interleaving via `compute_next`, fork into 0/1/N
successors); union the grow-only outputs; a configuration drains to `Valid` or
hits `Invalid`. The backends differ only in *where* the `step`s run and *how* the
continuations and the output union move between workers (shared memory, a
`postcard` round-trip, or MPI messages).

Every backend is pinned against the sequential oracle by
[`tests/parallel_oracle_crosscheck`](tests/parallel_oracle_crosscheck/main.rs)
(in-process, annotated + inferred programs, identical across worker counts) and,
for the real MPI paths, by [`tests/mpi_cluster`](tests/mpi_cluster/main.rs), which
launches the verifier under `mpirun` (each process a simulated node): the wave
backend at 1/4/24 ranks (checking it infers the oracle's configuration and
accessed byte-ranges), and the work-stealing backend at 8/16/24 ranks on the
larger `hpc_demo` program (self-checked against the single-process reference).
That output-level determinism rests on the six accumulators being
commutative-union monoids and configuration selection being by generator rank,
not completion order.

### 7.2 Performance: how each change scales compilation

The cost of verification is fixed by the program (the `n · h^r · 2^b · 8^v`
exponents of [§7](#7-the-cost-of-verification)); no engineering reduces it. What
the changes below do is let that fixed work be **spread over more hardware** and
**finish in less wall-clock**, while keeping the output bit-identical. Each change
removes one specific obstacle to that. The order matters: each depends on the ones
above it.

1. **Pointer-free `Continuation` + `AstNodeId` - the enabler.** Re-keying the
   frontier and the six accumulators on program-order `u32` indices (instead of
   `NonNull<AstNode>` / `*mut VerifierNode`) makes a frontier item `serde`/
   `postcard`-serialisable and position-independent. *Why it scales:* without it
   there is no distribution at all - you cannot ship a raw pointer to another
   process. It also makes every ordering key stable across machines, which is the
   precondition for independently-scheduled workers to agree on the output. *Cost:*
   one immutable AST image per rank; a re-key on each accumulator merge.

2. **Two-axis decoupling (outer config sweep vs inner fixed-config frontier) -
   exposing the parallelism.** The original `Explorerer` fused both axes into one
   chronological loop with a global `configuration` and **backtracking** - an
   inherently serial dependency, and the source of three serial hot-paths (a
   full-path `find_state` replay, a `state_cache.clear()` on every backtrack, a
   whole-frontier `invalid_path` scan). For a *fixed* configuration the inner
   search never backtracks (a failed check is just "invalid for this config"), so
   it becomes an embarrassingly-parallel tree expansion: any continuation can be
   stepped by any worker, in any order, with no shared mutable state. *Why it
   scales:* this is the change that turns one serial walk into N independent ones.
   The serial hot-paths disappear with the backtracking that needed them.

3. **Commutative-union monoid outputs - parallelism without coordination.** The six
   accumulators are grow-only sets merged by union (associative, commutative,
   idempotent); the winning configuration is chosen by generator rank (min), never
   by completion order. *Why it scales:* the result is therefore independent of how
   the work is partitioned, what order pieces finish in, or how many workers/ranks
   exist - so workers need **no** coordination to produce a deterministic answer,
   and the reduce can run as an unordered tree. Without this you would need a fixed
   global reduction order, which is itself a serial bottleneck. This is what makes
   "identical output at any worker/rank count" true rather than hoped-for.

4. **In-process rayon pool (`verify_configuration_parallel`) - all cores of one
   node.** A wave-synchronised BFS over the frontier across a work-stealing thread
   pool. *Why it scales:* a single configuration now uses every core on a node;
   speedup tracks core count until the frontier is narrower than the pool (ramp /
   tail) or the per-fork `State` clone dominates. *Limit:* one node; a barrier per
   wave; deep-clone cost per fork.

5. **Wave-synchronised MPI (`verify_configuration_mpi`) - more than one node.** Each
   wave, every rank steps its share (`index % size`) and an MPI all-gather rebuilds
   the frontier on every rank. *Why it scales:* it is the first backend that puts
   **one configuration's** frontier on many nodes. *What limits it, and motivates
   the next change:* (a) a **barrier every wave** - each wave waits for the slowest
   rank, so when per-rank work is uneven (which racy-interleaving subtrees always
   are - sibling branches differ by orders of magnitude in size) the fast ranks sit
   idle a large fraction of the time, and that idle fraction *grows* with both the
   imbalance and the rank count; (b) the frontier is **replicated** on every rank,
   so per-rank memory is the whole frontier (not `frontier/N`) and the all-gather
   moves the entire frontier every wave (bandwidth ∝ frontier-width × waves).

6. **Lifeline work-stealing + Mattern credit termination
   (`verify_configuration_mpi_stealing`) - load balance at scale.** Each rank owns a
   private deque (rank 0 seeded); an idle rank *steals* from its **lifeline**
   hypercube neighbours (`rank XOR 2^k`); there is no global barrier. Termination is
   detected by **Mattern's conserved-credit** scheme: credit starts at rank 0,
   travels with stolen work, and returns to rank 0 when a rank goes idle - all
   credit home means no rank holds work and none is in flight, so the search is
   globally done. Three distinct wins over the wave backend, each growing with
   scale:
   - **No barrier ⇒ no idle-waiting.** A rank that drains its subtree immediately
     steals more instead of waiting at a wave edge. Because the subtrees are wildly
     uneven, this reclaims exactly the fast-rank idle time the wave barrier wasted;
     the bigger the cluster and the imbalance, the larger the saving.
   - **Partitioned frontier ⇒ less memory and less traffic.** Each rank holds only
     its own deque (≈ `frontier/N`), so per-rank memory scales *down* with N.
     Continuations cross the wire only on an actual steal (an idle event), not the
     whole frontier every wave - bandwidth is proportional to steals, not to
     frontier-width × waves.
   - **`O(log N)` steal targeting and constant-size termination.** Lifeline
     neighbours bound steal fan-out to `log N` per idle rank (vs probing all N);
     Mattern credit is a handful of `u64` messages, so detecting global completion
     does not get more expensive as the frontier grows.

   *Measured* (`tests/hpc_demo`, a ~500k-continuation racy search): under `mpirun`
   the work-stealing inner search finishes in **~0.65 s across 16 ranks**, versus
   the **~10 s single-process reference** it self-checks against - the same answer,
   an order of magnitude faster. *When it does not pay:* tiny
   problems, where steal/termination overhead exceeds the work (`racy_store_inferred`
   completes in ~0 s either way), and oversubscribed hosts, where idle stealers would
   busy-spin - so the idle loop calls `yield_now` (a no-op with one rank per core,
   a core hand-off when ranks share one). The rough break-even is ~10³ fresh `step`s
   per inter-node steal.

A supporting change underpins 4-6: **`step_local` is the single work unit** (one
continuation → successors + terminal + outputs), shared verbatim by the rayon pool,
the transport simulation, and both MPI backends, so they provably compute the same
thing and the cross-checks are meaningful; continuations cross the wire as compact
`postcard` bytes. The honest limit on all of this is [§7](#7-the-cost-of-verification)'s
exponents: distribution buys a constant factor (more nodes finish the *same* work
sooner), never exponent relief - reducing `h^r·2^b·8^v` is a language/annotation
question ([§11](#11-design-notes--roadmap)), not a scheduling one.

### 7.3 Execution model at a glance

Condensing 7.1-7.2 into the two views most readers want.

**Stages of abstraction** (coarsest to finest; how work flows between them):

- **MPI world / cluster** - N ranks, each holding the same replicated,
  `AstNodeId`-indexed AST. The outer sweep splits candidate configurations across
  ranks (rank `r` takes `i % size == r`); an all-reduce(min) picks the lowest-rank
  valid one, the winning configuration.
- **Node / MPI rank** - one **single-threaded** process. Owns a private deque of
  continuations for the winning configuration, steps them one at a time, and when
  its deque empties steals half a deque from a lifeline hypercube neighbour
  (`rank XOR 2^k`), continuations crossing as `postcard` bytes; Mattern credit
  detects when every rank is idle. A node is saturated by running one rank per core.
- **Core / thread** - one thread per rank in the MPI backends (core ≡ rank). The
  separate in-process rayon backend instead runs *one* process across all cores,
  one worker per core pulling from a shared wave frontier; the two are not composed.
- **Continuation** - the dispatched work item: a pointer-free path state (`state` +
  per-hart `fronts` + `active_hart`). `step_local` turns one into 0/1/N successors,
  an optional terminal, and grow-only outputs reduced into the result by union.

**The broadly sequential start-up** (steps 1-8 are serial; the search fans out at 9):

1. Translate the `hl` source to the RISC-V dialect (prelude + lowered control flow).
2. Parse it into the program-order AST (`new_ast`).
3. Compact the AST by re-allocating its nodes freshly (`compress`).
4. Index it (`Ast::index`): give every node a stable program-order `AstNodeId` - the pointer-free key.
5. Replicate that image on every rank (deterministic: same source → same ids).
6. Enumerate candidate configurations (`candidate_configs`: `locality_list × type_list`).
7. Outer sweep: each rank verifies its share; all-reduce(min) selects the winning configuration.
8. Seed the inner frontier: one `Continuation` per system at the entry node (rank 0 holds them all, plus all the credit).
9. Fan out: ranks drain that frontier in parallel (work-stealing, or waves) - no longer sequential.

(The legacy sequential `compile()` path stops after step 3 and hands the raw AST to
the `Explorerer` oracle, which fuses the sweep and search into one backtracking loop.)

## 8. Key data structures (quick reference)

| Type                                                     | Location                                                                                                                          | Purpose                                                                                                                  |
| -------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------ |
| `TranslateError`                                         | [hl.rs:41](src/hl.rs#L41)                                                                                                         | `{ line, message }` for an `hl` translation failure (1-based line; `translate` never panics).                            |
| `AstNode` / `AstValue` / `Span`                          | [ast.rs:7](src/ast.rs#L7)                                                                                                         | Intrusive AST list node, value, source span.                                                                             |
| `Instruction`                                            | [ast.rs:177](src/ast.rs#L177)                                                                                                     | 27-variant tagged union of supported instructions/directives (incl. `ecall`).                                            |
| `Region` / `RegionBound` / `RegionPermissions`           | [ast.rs](src/ast.rs)                                                                                                              | The `#@` directive: region bounds (immediate/register) + `r`/`w`/`rw`.                                                   |
| `Type` / `FlatType` / `Locality`                         | [ast.rs:335](src/ast.rs#L335) / [276](src/ast.rs#L279) / [313](src/ast.rs#L316)                                                   | Compile-time types; `FlatType` is the runtime type-number encoding.                                                      |
| `Explorerer`                                             | [verifier.rs:150](src/verifier.rs#L150)                                                                                           | The verification state machine.                                                                                          |
| `VerifierNode` / `VerifierLeafNode`                      | [verifier.rs:114](src/verifier.rs#L114) / [99](src/verifier.rs#L131)                                                              | Execution-tree interior / frontier nodes.                                                                                |
| `ExplorePathResult`                                      | [verifier.rs:1708](src/verifier.rs#L1708)                                                                                         | `Valid` / `Invalid` / `Continue(self)`.                                                                                  |
| `ValidPathResult`                                        | [verifier.rs:1770](src/verifier.rs#L1770)                                                                                         | `{ configuration, touched, jumped, accessed, transitions, uncompactable, pinned_nodes }`; feeds the optimizer + codegen. |
| `AccessedRanges`                                         | [verifier_types.rs](src/verifier_types.rs)                                                                                        | `BTreeMap<Label, BTreeSet<(u64, u64)>>`: runtime-accessed bytes per region; drives dead-data elimination.                |
| `AccessTransitions`                                      | [verifier_types.rs](src/verifier_types.rs)                                                                                        | Per-node `(label, from, to)` pointer transitions; drives layout compaction's instruction rewriting.                      |
| `InnerVerifierConfiguration` / `Section` / `Permissions` | [verifier.rs:71](src/verifier.rs#L71) / [46](src/verifier.rs#L77) / [53](src/verifier.rs#L84)                                     | Per-system input: harts + memory map.                                                                                    |
| `MemoryValue`                                            | [verifier_types.rs:660](src/verifier_types.rs#L660)                                                                               | Universal symbolic value (ranges / list / ptr / csr).                                                                    |
| `MemoryLabel` / `MemoryPtr`                              | [verifier_types.rs:1235](src/verifier_types.rs#L1235) / [1189](src/verifier_types.rs#L1188)                                       | Label-tagged symbolic memory & pointers.                                                                                 |
| `State` / `MemoryMap` / `RegisterValues`                 | [verifier_types.rs:1554](src/verifier_types.rs#L1554) / [1260](src/verifier_types.rs#L1259) / [1552](src/verifier_types.rs#L1680) | Reconstructed machine state.                                                                                             |
| `TypeConfiguration` / `LabelLocality`                    | [verifier_types.rs:1726](src/verifier_types.rs#L1726) / [1573](src/verifier_types.rs#L1702)                                       | Inferred per-variable type+locality; the proof output.                                                                   |

## 9. Conventions & gotchas

- **Pervasive `unsafe` raw-pointer linked lists.** Both the AST
  (`Option<NonNull<AstNode>>`) and the verifier tree (`*mut VerifierNode` etc.)
  are hand-managed: `alloc`/`Box::into_raw` to allocate, manual `dealloc` to
  free. Correctness depends on hand-maintained invariants (e.g. exactly one node
  per hart before the root; the head/tail pointers are accurate). Almost every
  verifier function is `unsafe`.
- **Multi-hart front search is O(distance between harts).** `queue_up` finds each
  hart's current front by walking the verifier tree back from the leaf until it
  has seen all `harts` ([src/verifier.rs:1195](src/verifier.rs#L1195)). This is
  cheap when the harts advance together (e.g. a racy program where every hart
  branches often) but **O(N²)** for a **leader/worker** program where one hart
  runs a long solo stretch while the others sit parked far back: each step walks
  back past the whole stretch. `fannkuch_v2` is this case, which is why it keeps
  `n` small. The debug-only loop backstop is generous (1e9) rather than tight so
  the legitimate deep walk does not trip it; the real guard is the "reached root"
  check. A cached/incremental front map would remove the O(N²) (future work, part
  of the parallel rework).
- **One `AstNode` = one `Layout::new::<AstNode>()` allocation.** Every AST node is
  its own allocation: `new_ast` allocates them per node, `compress` re-allocates
  them per node, and the optimizer frees them per node (`remove_untouched` /
  `remove_branches`). Do **not** pack the nodes into a single `Layout::array`
  arena: a later per-node free would then free an interior pointer (a bad-free /
  heap corruption - exactly the bug a contiguous `compress` arena caused). The
  raw `dealloc`s never run `Drop`, so a node's `AstValue`-owned heap data is moved
  by `copy_to_nonoverlapping`, never double-freed.
- **Debug-only infinite-loop guards.** Many `while` loops over the lists carry
  `#[cfg(debug_assertions)] let mut check = (0..1000).into_iter();` with
  `debug_assert!(check.next().is_some());` (and `(0..100_000)` in a couple of
  places). These panic in debug builds if a loop exceeds the bound (cycle /
  corruption guard) and are **compiled out in release**: release builds can loop
  unboundedly on malformed structures. Preserve these when adding new traversals.
- **Error model: `verifier.rs` never panics.** Every former
  `todo!`/`unimplemented!`/`unreachable!`/`panic!`/`unwrap`/`expect` in
  [src/verifier.rs](src/verifier.rs) has been converted to return a
  [`CompilerError`](src/verifier.rs) (`Unsupported(String)` for a construct the
  verifier does not yet handle, the old `todo!`s; `Internal(String)` for a
  violated invariant, the old `unwrap`/`unreachable`/`panic`). `Explorerer::new`
  and `next_step` therefore return `Result<_, CompilerError>`, and the failure
  propagates to the caller (e.g. a test) alongside the trace, instead of aborting
  the process. A module-level `#![deny(clippy::unwrap_used, clippy::expect_used,
clippy::panic, clippy::todo, clippy::unimplemented, clippy::unreachable)]` at
  the top of the file enforces this; keep `verifier.rs` clippy-clean.
  - Helpers: `OrInternal::internal("ctx")?` converts an `Option`/`Result` into a
    `CompilerError::Internal` (the `?`-able replacement for `.unwrap()`);
    `check_store`/`check_load` return `Result<ControlFlow<ExplorePathResult,
Self>, CompilerError>` (continue / terminal-outcome in `Ok`, error in `Err`).
  - **Still panics: [src/verifier_types.rs](src/verifier_types.rs).** The
    value/memory model (and the parser in [src/ast.rs](src/ast.rs)) have **not**
    been converted: their internal `todo!`/`unwrap` still abort. A program that
    reaches one of those (e.g. unions, multi-element list slices, `.ascii`) will
    panic before `verifier.rs` can turn it into a `CompilerError`. Converting
    these is the remaining work to make the whole pipeline panic-free.
  - **Mixed-width integer arms.** The value model originally handled only the
    type pairs the early tests exercised (mostly `U8`/`U32`/`I8`). `fannkuch_redux`
    needs registers (`I64` from `li`/`addi`) to interoperate with 4-byte memory
    slots (`U32` from `lw`), so the following **additive** arms were filled in
    (each only fires on a path that previously `todo!`'d, so the pinned tests are
    untouched): `compare` gained `(U8,I64)`/`(I64,U8)`/`(I64,U32)`; `MemoryValue::set`
    gained the `(I64,U32)` interior-element truncation and the matching
    end-of-list (`Ordering::Equal`) coercion (a register value is wider than the
    slot it lands in, so its low `len` native-endian bytes are kept); `MemoryValue`'s
    `Add` for `(U32,I64)` now **promotes to `I64`** (RV64 registers are 64-bit, so
    `lw`-then-`addi` widens, and a negative immediate no longer underflows an
    unsigned slot); and `queue_up`'s `bnez`/`beqz` branch resolution gained
    `U32`/`U64`/`I64` zero-comparison arms (the two-operand branches already used
    the generic `compare`). The same class of gap will resurface for any new
    type pairing a future program exercises.
- **Parser fragility.** Operands are sliced at fixed offsets (2-char registers,
  single space after commas); only 8 register names parse; `Span::row`/`column`
  re-read the whole source file from disk on every call and `.unwrap()` the IO.
- **Windows newlines.** Parsing and `print_ast` both special-case `\r\n`; the
  tests normalize via `normalize()` so the `\n`-based expected strings are
  portable. The canonical printed form makes the zero offset explicit
  (`sw t1, (t0)` parses and prints back as `sw t1, 0(t0)`), so expected strings
  must use `0(t0)`, matching [tests/uart_hello/ast.s](tests/uart_hello/ast.s).
- **`dialect.s` files are generated, never hand-edited.** Each is pinned as
  `hl::translate(input.hl)`'s exact output; to change a test program edit its
  `input.hl` and regenerate (`cargo run --example translate -- …`, see [§5.1](#51-the-hl-front-end)).
  On Windows the generated file is CRLF (the dialect parser requires the
  platform newline); keep it that way when committing.
- **`hl` dispatch order.** In `statement`, assignments are matched _before_
  the `name: <locality> <type>` define form: a slice store (`t0[0:4] = t1`)
  contains a `:` and would otherwise be taken for a definition. Preserve this
  order when adding statement forms. The surface language has **no `goto` and
  no bare labels** (control flow is `if`/`while` blocks plus `require`); the
  dialect's labels are generated (`_l0`, …).
- **Tests pin exact incremental behaviour (brittle by design).** `racy_store_inferred`/`racy_store_annotated`
  assert the full per-step trace; `racy_increment`/`uart_hello` assert the exact step count and
  type-inference timeline; all assert the exact `TypeConfiguration` and optimized
  `print_ast` output. A behavioural change to parsing, inference, interleaving or
  optimization will (correctly) break them; re-baseline deliberately (re-derive
  the expected values from the new behaviour), never by loosening the assertions.
  These are stable contracts only because exploration is deterministic; keep it
  that way (see the determinism note in [§4.3](#43-verification--explorerer)).
- **Manual `dealloc` layouts must match the type.** `invalid_path`'s
  encounter-subtree DFS frees `VerifierNode`s and `VerifierLeafNode`s with
  _different_ sizes: each must use its own `Layout`. (A prior bug freed a
  `*mut VerifierNode` with `Layout::new::<VerifierLeafNode>()`; benign while
  exploration rarely backtracked at the root, but it corrupted the heap once
  first-line encounters made root rebuilds frequent. Now fixed; keep node and
  leaf deallocations on their own layouts.)
- **`accessed`/`transitions` are bookkeeping, never control flow.** The
  dead-data ranges and pointer transitions (recorded into the `Explorerer`
  unions via `RecordSinks`) must stay over-approximating: record with the full
  symbolic offset span, record at _every_ application site, and never branch
  on the contents during exploration (that would couple step order to
  bookkeeping and could break determinism). When adding a new load/store or
  pointer-arithmetic form, add **both** its `record_access` and
  `record_transition` calls. A missed access record means codegen may elide a
  live byte, and a missed transition means compaction may move bytes without
  re-pointing the instruction: both produce a _wrong program_, not a test
  failure. (Recording a transition with a non-exact offset safely demotes the
  region to the padded layout instead.)
- **`From<MemoryValue> for Type` vs `From<&MemoryValue> for Type`** disagree for
  `Ptr` (`I64` by value, `U64` by reference); be deliberate about which you call.
- **`Locality` discriminants are reversed** vs declaration order
  (`Thread = 1`, `Global = 0`).
- **Stray output**: an unconditional `println!` debug block sits in
  `MemoryValue::set` near [src/verifier_types.rs](src/verifier_types.rs).

## 10. Known limitations & TODO map

The most impactful in-code TODOs/limitations (search the files for the rest):

- `formal::compile` ([§4.9](#49-the-compile-api--the-formal-cli)) hard-codes the
  verifier config (one hart, no `#@`/MMIO sections): enough for a hosted program
  (the `print`/`exit` standard library reaches the outside through `ecall`), but
  a bare-metal program with regions or multiple harts needs the lower-level
  `Explorerer` API with the right systems. Threading a config through `compile`
  (and the generated build script) is future work.
- Raw-`I64`-address **loads** always read as a full-range (unknown) value of
  the loaded width: stored values are not tracked through heap memory, so a
  program cannot yet _branch_ on a value it stored to a `#@` region (the
  comparison is indeterminate → `Unsupported`).
- Register-defined `#@` bounds use plain interval arithmetic (`end - start`),
  which loses the correlation between the two bounds: regions with genuinely
  under-determined bases verify conservatively (or hit the indeterminate
  section comparison). Relational tracking is future work; today an
  allocator's `#@ t0 t1 rw` works when the bounds are path-exact.
- Layout compaction ignores **alignment**: removing bytes can move an access to
  a misaligned address (QEMU emulates this; stricter RISC-V hardware traps). An
  alignment-preserving mode would keep gaps `mod` the access width.
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
  subtypes pointer: a verified program that follows it would dereference 0 at
  runtime. Emitting nested descriptors (or rejecting them in codegen) is open.
- Multi-element list slice get/set returns `ListMultiple` (unimplemented;
  `covers` is collected but never applied).
- `.ascii` parsing (`new_ascii`) is entirely `todo!()`.
- `wfi` is modeled as racy (over-approximation → some valid programs rejected,
  slower exploration); interrupt state is unmodeled.
- `partial`/`sequential`/`typed`/`racy-groups` compiler modes and the
  list/union exploration CLI args (`list_depth`, `list_width`, `union_depth`)
  are designed but not implemented; see [§11](#11-design-notes--roadmap).

<a id="11-design-notes--roadmap"></a>

## 11. Design notes & roadmap

Longer-form design intent, kept beside the precise description above so the
two stay in one place.

### Scaling modes (designed, not implemented)

Configuration arguments that trade the §7 exponents away when a program (or a
build profile) can afford weaker guarantees:

- `racy-groups <n>`: treat runs of ≤ `n` adjacent racy instructions as one
  unit when enumerating interleavings. A heuristic (nearby instructions almost
  always run back-to-back), so it trades soundness for a large cut of `h^r`;
  interactions with syscalls/interrupts are unresolved (bare-metal focus makes
  this tolerable for now).
- `sequential`: explore a single instruction ordering, removing `h^r`
  entirely (single-hart semantics).
- `typed`: require every variable's type to be immediately inferable
  (`#$ x global u32`-style), removing `8^v`; inference degrades to the
  local/incomplete kind conventional languages have.
- `partial`: allow partial exploration, where untouched code is kept rather than
  proven-dead, and each `#!` becomes a unique runtime error code (Zig-style
  errors) instead of a proof obligation.
- Exploration bounds as CLI args: hart range to verify; `list_depth` /
  `list_width` / `union_depth` for bounded list/union type exploration
  (today lists/unions must be written explicitly in `#$`); the memory
  `Section`s a system provides (today supplied by the test harness).

### Memory placement (future)

Today every inferred variable is zero-initialized storage in `.bss` (one copy
per hart for `thread` locality) and descriptors are `.data`. The fuller design:
initialized data → `.data`, initialized read-only → `.rodata`, uninitialized →
`.bss`; a `tls` option choosing real `.tdata`/`.tbss` thread-local storage
(isolation) versus plain per-hart copies (memory efficiency); and a `local`
locality placed on the stack for non-static lifetimes. Thread-local data in
ordinary global memory is still _physically_ racy; the non-racy treatment is
justified by the single-accessor assumption, which a future mode could verify
or relax.

### Borrow checking as a library

Borrow checking is, from this verifier's perspective, just a way to invalidate
bad paths faster: implement a reference-counted pointer whose invariant is a
`#!` the proof must show unreachable, and using it everywhere recovers
borrow-checker economics (no races ⇒ `h^r` collapses ⇒ small-hart proofs
generalize) while keeping exact interleaving verification available where racy
code is intentional. [comparison.md](comparison.md) develops this "dial" at
length.

### Dead compile-time data: the long-term picture

§4.3/§4.8 describe the implemented mechanism (accessed-ranges + transitions →
compaction). The general principle it serves: information consumed only by the
verifier must not exist in the output. A variable without an exact address
lives at a _symbolic_ address; an access either provably stays inside it (so
the verifier knows exactly which bytes exist at runtime) or cannot be verified
at all. If a runtime read of some bytes survives (e.g. through `#&`), those
bytes are emitted; if every consumer of a byte was resolved at compile time
(an `if` on locality, a length check against a constant), it is not. The
remaining gap is alignment-preserving compaction (§10).

### Further output optimizations (beyond `remove_untouched`/`remove_branches`)

3. Remove writes to registers that are never read (initially assuming syscalls
   read everything; later a per-syscall register-effect model).
4. Remove memory writes that are never read (requires the volatile/MMIO
   modelling `#@`'s `Section.volatile` already begins).

### The Python-like layer (started: [src/hl.rs](src/hl.rs))

The language users are meant to write is the Python-like layer ([§5.1](#51-the-hl-front-end)),
not the dialect; the dialect is its verification/compilation target. The
non-negotiable property as the layer grows (expressions, control-flow sugar,
more builtins): translation must stay **simple and cheap**, near one-to-one
the way C maps onto assembly, so the cost model and the verifier's view of the
program remain legible from the source. Inline assembly stays available via
the `asm:` block (spelled like `if:`), so nothing expressible in the dialect
is ever out of reach. The language's name is still undecided.

### Ambitions

The motivating end-states for the language: a bare-metal OS running DOOM; a
bare-metal Tor node; a bare-metal web server; a bare-metal level-1 hypervisor
as the base of a serverless platform. RISC-V only (aarch64 undecided, x86-64
never). Languages worth stealing from: Lean, Rust, Zig, OCaml, Ada, Mojo,
Python.
