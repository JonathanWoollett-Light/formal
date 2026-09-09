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
  `Invalid`), and `element_inference`/`element_mixed`/`element_refusals`
  pin what element indexing resolves to and the two ways it is refused. See
  [§6](#6-integration-tests-tests).
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
and installs the system dependencies the tests and the distributed backend need
(WSL on Windows, `qemu-system-riscv64`, the RISC-V GNU toolchain, a system MPI
library), escalating where required (a UAC dialog for installing WSL itself,
`wsl -u root` / `sudo` for the apt packages). When a step needs a reboot to
finish (installing WSL; an apt install that newly leaves
`/var/run/reboot-required`), it asks `[y/N]` on the console device
(`CONIN$`/`/dev/tty`, since Cargo captures build-script output), schedules
`cargo build` to re-run at the next login (an `HKCU` RunOnce entry on Windows;
on Linux a self-removing hook in the login-shell rc files, which expires after
two weeks if it never fires), and reboots; being idempotent, the re-run
continues where it left off.
It never fails the build, and never prompts under `CI` or without a console;
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
cargo nextest run --run-ignored all -E 'test(factory_default_linux)'
                      # factory-default setup e2e in a VM (§6.2; ~3 min)
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
line-poking. The baseline is ~83% of regions / ~84% of lines (`codegen.rs` ~95%,
`lib.rs` ~97%, `hl.rs` ~93% via `tests/compile_api` exercising `formal::compile`
and `tests/translate_errors` exercising the front-end's rejection paths;
`main.rs` ~92% via `tests/cli` running the binary). The signed-arithmetic
programs (`signed_bytes`/`signed_words`/`signed_max`/`dot_product`/`difference_array`)
fill the `i8`/`i32` value-model arms with real computations, and
`halfword_sum`/`signed_halfwords` the `u16`/`i16` ones (via 2-byte `lh`/`sh`). The little proven-correct algorithm
programs (`fannkuch_redux`, `sieve`, `bubble_sort`, `collatz`, `sentinel_sum`,
`inferred_widening`, the `reg_*` and `indexed` arithmetic tests) are what cover
the verifier's branch resolution, type inference and interval arithmetic from
real code rather than line-poking. `src/draw.rs` (an unreferenced verifier-tree visualisation
helper with no public API) is excluded from the measurement - covering dead code
would mean tests that exist only to move the number. The largest remaining gap is
in `verifier_types.rs`/`verifier.rs`: those are mostly the **value/arithmetic
paths for type/operation combinations the language does not implement yet**. The
register-register arithmetic set (`add`/`sub`/`mul`/`div`/`rem`) and indexed
addressing have since landed (with the `reg_*`/`indexed` tests), so those paths
are now covered, and element indexing closed the width/sign mixes wholesale (a
whole-scalar store/load of any width, and scalar comparison and arithmetic over
any pair, are generic rather than a table of hand-written pairs); what remains
uncovered is the rarer combinations that still `panic` on a `todo!` (unions,
multi-element list slices, partial stores that straddle a scalar, `.ascii`). They are deliberately uncovered until the feature lands, so coverage
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

```text
.
├── build.rs                   # the setup entry point: installs the system deps (§2)
├── Cargo.toml                 # manifest; `[profile.test] opt-level = 3` (§2)
├── .cargo/config.toml         # `cargo nt`/`cargo cov` aliases, nextest config (§2)
├── .github/workflows/         # CI (`ci.yml`, `comparisons.yml`, `setup-e2e.yml`)
├── src/                       # the compiler (library + `formal` binary)
│   ├── lib.rs                 # library root: modules, `compress`, `print_ast`
│   ├── main.rs                # the `formal` CLI: `formal new <name>` (§4.9)
│   ├── hl.rs                  # `hl` front-end: one statement -> one dialect line (§5.1)
│   ├── ast.rs                 # lexer/parser: `AstNode` list, `Instruction`, operands
│   ├── verifier.rs            # the sequential `Explorerer`, the verification oracle
│   ├── verifier_types.rs      # symbolic value & memory model; no `unsafe`
│   ├── explore.rs             # pointer-free parallel exploration + config sweep (§7)
│   ├── dist.rs                # the distributed MPI backend (`--features hpc`, §7)
│   ├── optimizer.rs           # post-proof `remove_untouched` / `remove_branches`
│   ├── codegen.rs             # `emit_executable`: AST + inferred layout -> RISC-V
│   └── draw.rs                # `draw_tree`: ASCII tree rendering (debug)
├── std/
│   └── std.hl                 # stdlib prelude prepended to every program (§5.1)
├── examples/
│   ├── translate.rs           # regenerate a test's `dialect.s` via `hl::translate`
│   ├── compile.rs             # scratch driver: an `hl` file -> dialect + assembly
│   └── update_website.rs      # re-inject `metrics.prom` into `index.html` (§6.1)
├── tests/                     # integration tests, one folder per pinned behaviour (§6)
│   ├── common/mod.rs          # the shared test helpers
│   ├── <name>/                # `main.rs` + its assets (`input.hl`, `dialect.s`,
│   │                          #   stage pins); Valid-outcome tests boot in QEMU
│   └── comparisons/           # language-comparison pipeline (§6.1): other languages'
│                              #   sources + committed-but-generated `metrics.prom`
├── scripts/
│   └── build-run.sh           # `as`/`ld` + boot `target/gen/*.s` in QEMU
├── tools/
│   └── qemu-plugin/           # `formal_stats.c`: measures instructions + memory (§6)
├── assets/                    # scratch inputs (`one.s`, `two.s`)
├── deploy/                    # k8s + Kubeflow MPI Operator target for `hpc` (§7)
├── comparison.md              # vs Python/C/C++/Rust/Zig/Lean/Ada-SPARK
├── index.html                 # the website (§6.3); `COMPARISON-DATA` is generated (§6.1)
├── website.md                 # the edit/verify loop for `index.html` (§6.3)
├── TODO.md                    # short/medium/long-term TODOs
├── README.md                  # user instructions: setup, install, hello world
├── CLAUDE.md                  # generic rules + the documentation separation
└── DEVELOPMENT.md             # this document
```

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
uncompactable, pinned_nodes, indexed }`.
2. Pop (peek) the front leaf; mark its AST node in `touched`.
3. Dispatch on the instruction:
   - `Lidx` / `Sidx`: `resolve_index(..)` against the pointee's type, then the
     same check as the sized load/store it resolves to; an index past the end
     is invalid, a pointee with no element type (a raw address) is refused.
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
`accessed: AccessedRanges` (runtime-accessed bytes per region), the layout
compaction inputs `transitions` / `uncompactable` / `pinned_nodes`, and
`indexed: IndexLowerings` (what each element-indexed access resolved to);
together these drive dead-data elimination and the element expansion in codegen,
[§4.8](#48-code-generation--emit_executable-srccodegenrs).

`indexed` is the one record that is **not** monotone. The others may keep
entries from since-abandoned configurations, which only over-approximates (more
bytes kept alive, more regions left padded). A lowering cannot work that way:
one directive becomes one instruction, so a width left over from a rejected
candidate type would be a *wrong* instruction, not a conservative one. So
`invalid_path` drops the lowerings recorded against the variable it re-types,
and the replay past that variable's first encounter records them afresh under
the new type. `element_inference` ([§6](#6-integration-tests-tests)) is the
test that would fail if it did not: its `accessed` still carries the rejected
`u8` candidate's byte, while its emitted program is the `u16` pair.

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
  [src/verifier_types.rs:870](src/verifier_types.rs#L870)). A typed-list store
  whose **offset is a range** (a computed, runtime-dependent address such as
  `runtime_input`'s) applies the flank-preserving weak update
  (`ranged_weak_update`): every scalar element the maximal span
  `offset.start .. offset.stop + len` may touch havocs to its full type range
  (the sound union of "old value or new value"), elements outside the span
  keep their values, and a covered non-scalar stays unsupported
  (`ListMultiple`). Raw `I64`-addressed
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
- **Expands the element-indexed accesses** (`#[` / `#]`) into the sized
  instruction each stands for. The directive carries an element index; the
  *proof* carries what that index means, as `indexed: IndexLowerings` (per node,
  the `(label, element type, byte offset from the pointer)` every execution
  resolved to). Codegen takes the single lowering a node agreed on, applies the
  same compaction rewrite as any other access, and picks the mnemonic from the
  element's **type**, so the load extends the way the verifier modelled the
  value: `lbu`/`lhu`/`lwu` for `u8`/`u16`/`u32`, `lb`/`lh`/`lw` for the signed
  types, `ld` for 8 bytes, and `sb`/`sh`/`sw` for stores. This is the
  extraction split the design intends (the verifier checks a model, codegen's
  fixed expansion is trusted, like the TLS `la` expansion): a node with no
  lowering, or with two, emits `.err` so the assembler fails rather than the
  program silently losing an access. A node resolving two ways is refused, not
  chosen between; a wide (8-byte) element *store* is refused during
  verification, since the dialect has no `sd` yet.
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
- **Per-hart thread-local storage.** The verifier already models a `thread`
  variable as a distinct copy per contiguous hart index (`MemoryLabel::Thread {
  label, hart }`); codegen reproduces that at runtime. When a `thread` variable
  with real storage is used by **more than one hart**, all thread-locals are laid
  out as one 8-aligned block, the block is replicated once per hart, and a boot
  prologue sets `tp = mhartid * block_size` (mhartid is the contiguous hart index
  on the targeted platforms); each `la` of a thread-local then adds `tp`, so hart
  `h`'s copy is `label + h*block_size`. This is inert for single-hart use (one
  copy, `tp = 0`) and for descriptor-only reads (empty block), so those programs
  emit exactly as before. Without it, concurrent harts would share one fixed
  address and clobber each other; the `tls_probe` test pins the runtime behaviour.
  This is what lets a multi-hart program keep private per-hart `thread` arrays
  (e.g. a real parallel work-sharing computation, rather than the leader/worker
  pattern where only one hart touches thread-local memory).
- **Hosted multi-hart (`emit_executable_hosted`, `Target::HostedLinux`).** The
  same verified body can instead be lowered to run under **user-mode
  `qemu-riscv64`** (hosted Linux), where there is no `-smp` to start the other
  harts and `mhartid` is illegal. Codegen then emits a `_start` that sets hart
  0's `tp = 0` and spawns one OS thread per *extra* hart with the `clone` syscall
  (the glibc thread flag set `0x7d0f00`, which is what qemu-user accepts), giving
  each thread its own `.bss` stack and `tp = h*block_size` via `CLONE_SETTLS`;
  the child resumes after the `ecall` and jumps to the shared body, the parent
  spawns the rest then joins it. Program end (`unreachable`) becomes the `exit`
  thread syscall instead of the `wfi` halt loop, so the process ends once every
  hart's thread has exited (with whatever the finishing hart printed). Everything
  else (the TLS block layout, the `la`+`add tp` per thread-local) is identical to
  bare metal. This gives **real parallelism** (the harts run on separate cores
  under qemu-user MTTCG, not `-smp` round-robin), which is how `fannkuch_v2` runs
  far faster hosted than bare-metal; its fences (`fence rw, rw`) already make it
  correct under that weaker ordering. `emit_executable` (bare metal) is unchanged
  and byte-identical to before.

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
`tests/common/mod.rs`, assembles + links + boots it (through WSL on Windows, or
directly under `bash` on a native unix host -- see `toolchain_shell` in
`common/mod.rs`), asserting **no CPU fault** (and that `uart_hello` writes
`Hello World!` to the UART). The toolchain and QEMU are **required**: the tests
**fail** (not skip) if the toolchain / QEMU are absent; point `RISCV_BIN` at the
toolchain `bin/` (default `$HOME/riscv-toolchain/riscv/bin` on Windows, or the
`PATH`-resolved `riscv64-unknown-elf-*` on a unix host). [scripts/build-run.sh](scripts/build-run.sh)
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

| `hl` statement                                   | Dialect line                                                                     |
| ------------------------------------------------ | -------------------------------------------------------------------------------- |
| `value: global _` / `welcome: _ [u8*13]`         | `#$ value global _` / `#$ welcome _ [u8 u8 … u8]` (a define; lists expand below) |
| `t0 = &value`                                    | `la t0, value`                                                                   |
| `t0 = type(welcome)`                             | `#& t0, welcome`                                                                 |
| `t0 = csr(mhartid)`                              | `csrr t0, mhartid`                                                               |
| `t1 = 0x10000000`                                | `li t1, 0x10000000` (radix text preserved)                                       |
| `t2 = t1`                                        | `addi t2, t1, 0` (register move)                                                 |
| `t1 = t1 + 1` / `t1 = t1 - 8`                    | `addi t1, t1, 1` / `addi t1, t1, -8` (immediate `+`/`-` only)                    |
| `t3 = t1 + t2` / `t3 = t1 - t2`                  | `add t3, t1, t2` / `sub t3, t1, t2` (register-register)                          |
| `t3 = t1 * t2` / `t3 = t1 / t2` / `t3 = t1 % t2` | `mul` / `div` / `rem t3, t1, t2` (register-register; no immediate forms)         |
| `t0[0] = t1` / `t1 = t0[2]`                      | `#] t1, 0(t0)` / `#[ t1, 2(t0)` (element store/load; see below)                  |
| `t0[0:4] = t1`                                   | `sw t1, 0(t0)` (raw store; width 1 = `sb`, 2 = `sh`, 4 = `sw`)                   |
| `t1 = t0[8:16]`                                  | `ld t1, 8(t0)` (raw load; width 1 = `lb`, 2 = `lh`, 4 = `lw`, 8 = `ld`)          |
| `forget t0`                                      | `#~ t0` (havoc: `t0` becomes *any* value; emits nothing)                         |
| `section 0x100 0x200 rw`                         | `#@ 0x100 0x200 rw`                                                              |
| `fail` / `unreachable`                           | `#!` / `#?`                                                                      |
| `asm:` + indented lines                          | each block line emitted verbatim (inline assembly; an empty block is an error)   |

A define may carry a **list initialiser**, `name: <locality> [t*n] = [v, ...]`,
which is the one statement that lowers to more than one line:

```text
nums: thread [u32]*4 = [2, 7, 11, 15]
      ->  #$ nums thread [u32 u32 u32 u32]
          la t0, nums
          li t1, 2
          #] t1, 0(t0)
          ... one `li` + element store per value
```

Byte for byte what writing the stores out by hand lowers to, and visible in the
emitted output, which is the condition [§11](#11-design-notes--roadmap)'s cost
contract puts on a multi-instruction lowering (the string-literal `def`
argument set the precedent). It **clobbers `t0` and `t1`**, so an initialiser
that has to preserve them is written out by hand. The value count must equal
the type's element count, the values are integer literals (radix preserved),
and the type must be a list: scalars have no initialiser form. The statement
may **span lines** while its bracket is open, so a fixture can be laid out in
the shape of its data (`num_islands` writes its grid a row per line); nothing
else in the language spans lines.

In the define row, a `name:` with an annotation is a define, and a list type is
comma-separated **runs** `<scalar>*<count>` with `*` binding tightly, e.g.
`[u8*13]` or `[u8*2, u16*2, u8*3]` (a plain element is a run of 1); the legacy
outer `[t, t]*n` suffix cycles the whole list, so `[u8]*13` == `[u8*13]`.
Counts are plain digits, the expansion is capped at 2^24 elements, and every
form expands to the space-separated flat dialect list.

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

**Indexing is element-based.** `t0[k]` is element `k` of whatever `t0` points
at: `counter: thread [u32]*1` is written to with `t0[0] = t1` and an array's
third element is `t0[2]`, with no widths in the source. The front-end is
stateless and does not track what a register points at, so it lowers the access
to the `#[` / `#]` directives ([§5.2](#52-the-risc-v-dialect-as-actually-parsed))
and the **verifier** resolves each one: it alone knows every pointer's pointee
type, per state and (for an inferred variable) per type configuration. The
resolution is `(byte offset from the pointer, element type)`, the bounds check
is the existing access-past-the-label check applied to it, and codegen expands
the directive into the sized instruction it stands for
([§4.8](#48-code-generation--emit_executable-srccodegenrs)). A *runtime* index
is refused for now: compute the address (`t = i * <element size>`,
`p = base + t`) and index that with `p[0]`.

`reg[a:b]` is the **raw byte slice**, kept for memory that has no element type
of its own: a memory-mapped address, a `#@` region, or a variable whose type
the verifier is still inferring (there the access width is exactly what drives
the inference, so stating it is the point). It lowers directly to one sized
instruction, the width visible at the call site.

The two forms differ in what they can prove and what they emit. An element
access is bounds-checked at element granularity (`arr[2]` on a two-element
array is `Invalid`, at compile time, never a runtime check), it needs no width
in the source (so type inference is free to pick the narrowest type under which
the program is *provable*, see `element_inference` in
[§6](#6-integration-tests-tests)), and it knows the element's **type**, so its
load extends the way the verifier modelled the value (`lbu` for a `u8`, `lb`
for an `i8`). A byte slice knows none of that; it states a width and gets it.

`#` starts a comment exactly as in Python; comments and blank lines do not
appear in the output. Output
formatting matches `print_ast`'s canonical form ([§4.7](#47-serialization--print_ast-srclibrs65)):
instructions/directives indented four spaces, labels at column zero, platform
line ending (`\r\n` on Windows, which the dialect parser requires there).
Errors are `TranslateError { line, message }` (1-based line; no panics).

**A runtime index** is still built from the register-register multiply and add:
`arr[i] = v` (u32 elements) is written `t = i * 4; p = &arr + t; p[0] = v` (see
the `indexed` test). Keeping that explicit means the cost (a `mul` + an `add`)
stays visible in the source, and the element access at the end costs nothing
extra: for a pointee of uniform element width the resolution does not depend on
where in the variable the pointer sits, so `p[0]` resolves the same on every
path, including when `p`'s offset is only known as a range (`runtime_input`).
Folding that address arithmetic into `arr[i]` is the next step and needs a
decision the language has not made (which register the expansion may clobber,
[§11](#11-design-notes--roadmap)).

Resolving against a **mixed** shape (`[u8*2, u16*2]`, a descriptor record) does
depend on where the pointer sits: which element `k` steps on differs, so the
pointer's offset must be exact and on an element boundary, and the refusal says
so when it is not. `uart_hello` walks a descriptor record that way: after
`t0 = t0 + 16`, `t0[0]` is the record's length field (element 2), because
element 0 is always the element *at* the pointer.

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
matched **before** the `name: <locality> <type>` define form because a raw
slice store like `t0[0:4] = t1` contains a `:` and would otherwise parse as a
definition. (An element store, `t0[0] = t1`, has no colon and is not ambiguous;
the ordering is load-bearing only while the raw form exists.)

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

The integer arm lays a zero digit down before the peeling loop, because that
loop never runs for a zero argument and `print(0)` would otherwise write an
empty slice (`print_zero` pins this). It still **assumes a non-negative value**:
RISC-V `rem` takes the dividend's sign, so a negative argument formats from a
negative remainder and prints punctuation. Signed handling is future work, and
would cost two more clobbered registers. The clobber lists are part of the
contract, since a call is inlined into the caller's register file: the string
arm clobbers `a0`, `a1`, `a2`, `a7` and `t0`; the integer arm those plus `t1`,
`t2` and `t5`. `merge_intervals` ([§6](#6-integration-tests-tests)) is the
worked example of a loop that prints from registers the call leaves alone.

<a id="52-the-risc-v-dialect-as-actually-parsed"></a>

### 5.2 The RISC-V dialect (as actually parsed)

- **Directives**: `#!` `Fail`, `#?` `Unreachable`, `#$ <label> <locality> <type>`
  `Define`, `#& <reg>, <label>` `Lat`, `#@ <start> <end> <perms>` `Region`
  (keyword `section`; declare an accessible memory region: bounds are immediates or registers,
  `end` exclusive, perms `r`/`w`/`rw`; executed in program order, so an
  allocator can declare each allocation as it makes it), `#~ <reg>` `Forget`
  (havoc a register to *any* value; verifier-only, codegen drops it), and
  `#(` / `#)` `Assume` (bracket a block the verifier executes to narrow state and
  codegen drops; the `assume:` escape hatch), and the element-indexed access pair
  `#[ <rd>, <k>(<rs>)` `Lidx` / `#] <rs2>, <k>(<rs1>)` `Sidx` (`rd = rs[k]` /
  `rs1[k] = rs2`, where `k` counts **elements** of the pointee's type). The
  index pair is the one directive that becomes a real instruction chosen by the
  *proof*: the verifier resolves `k` against the pointee's type to a byte offset
  and an element type, and codegen emits the sized load/store
  ([§4.8](#48-code-generation--emit_executable-srccodegenrs)). Plain `#…`
  comments and inline `# …` comments are stripped.
- **Instructions** (`Instruction` enum, [src/ast.rs:260](src/ast.rs#L260), 42
  variants): `csrr`, `bnez`, `j`, `wfi`, `ecall`, labels (`foo:`), `.global`,
  `.data`, `.ascii` (parser is `todo!()`), `la`, `li`, `sw`, `lw`, `sh`, `lh`
  (2-byte halfword store/load, for `u16`/`i16`), `addi`,
  `add`, `sub`, `mul`, `div`, `rem` (register-register RV64M arithmetic),
  `amoadd.w rd, rs2, (rs1)` (RV64A atomic fetch-add, the lock-free
  work-claiming primitive: `rd = mem[rs1]; mem[rs1] += rs2` in one racy step),
  `blt`, `lb`, `beqz`, `sb`, `bge`, `ld`, `bne`, `beq`, plus the directives
  above. There is no `amoadd.w` surface form; it is written in an `asm:` block
  and parsed back from the emitted dialect (so the verifier models it, rather
  than treating the `asm:` block as opaque). `ecall` is the boundary to the host/OS: the verifier does not model
  its semantics (it is a no-op for checking and non-racy), but applying it
  **havocs `a0`** to the full range: the Linux ABI clobbers `a0` with the
  syscall's result, and pretending the old value survived would be unsound.
  Codegen emits it verbatim, so the syscall ABI otherwise lives entirely in
  the registers the surrounding code sets (the std `print`'s `write`, and a
  program's `exit`). Memory a syscall may write (`read(2)` into a buffer) is
  not modeled: consume such input through a raw `#@` section (whose loads
  return full-range values) until a `forget <label>` region havoc exists.
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
re-exported at the crate root. The one exception: a small `#[cfg(test)]` unit
module inside [src/verifier_types.rs](src/verifier_types.rs) pins the interval
transfer functions that private helpers implement (`rem_by_constant`'s
signed-rem envelope, exhaustively cross-checked against `i64` `%`, and the
ranged-store weak update), which no integration test can reach directly.

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
  The next two runners are the two **execution streams** (§11, _Execution
  models_):
- `run_program(name, ast, configuration, accessed, transitions, uncompactable,
pinned_nodes)` / `run_in_qemu(name, asm)` (the **bare-metal** stream):
  lower the optimized program with `emit_executable`, assert **no
  compile-time-only data leaked** (no `.byte` locality directives survive in the
  generated `.data`/`.bss`; none of these programs read locality at runtime),
  then assemble + link + **boot it in QEMU under WSL** (`qemu-system-riscv64
  -machine virt`), asserting no CPU fault and returning the captured UART output.
  The toolchain + QEMU are **required**: these panic (fail the test) if WSL / the
  toolchain / QEMU are missing (see §4.8). This stream is for what genuinely needs
  bare metal: MMIO devices, raw `#@` regions, multi-hart racy code, machine-mode
  CSRs (`mhartid`), and per-hart thread-local storage.
- `run_linux(name, asm)` (the **hosted-Linux** stream): builds a **static ELF**
  (entry `_start`, no fixed text address) and runs it under the user-mode
  emulator `qemu-riscv64` (bundled in the toolchain `bin/`, invoked as
  `$RISCV_BIN/qemu-riscv64`), returning its **stdout**. It **detects a guest
  crash** (a target signal / exit ≥ 128) and fails the test, so a program that is
  not actually hostable (e.g. it reads `mhartid` or uses multi-hart TLS, both
  illegal in user mode) cannot silently pass with empty output and a bogus
  near-zero instruction count. This is the default for anything hostable: it is
  far faster than full-system emulation, so the `formal_stats` plugin's runtime
  numbers (instructions / memory / wall-clock) are cheap and representative. Same
  required-not-skipped policy as `run_in_qemu`.
- **Runtime instrumentation (the `formal_stats` QEMU plugin).** Every QEMU boot
  (system-mode `run_in_qemu` _and_ user-mode `run_linux`) is instrumented by a
  small TCG plugin, [tools/qemu-plugin/formal_stats.c](tools/qemu-plugin/formal_stats.c),
  which reports the **exact guest instruction count** (per-hart, summed) and the
  **guest memory working set over execution time** (each time the set of distinct
  4 KiB pages the guest touches - instruction fetches + non-IO data accesses -
  grows, it records `(instructions so far, page count)`, so the host can derive
  the peak footprint and the **time-weighted percentiles of memory usage**). The
  host also times the QEMU invocation. These land in [`QemuStats`] on
  `QemuOutcome`, are echoed via `eprintln!` (visible with nextest `--no-capture`),
  and are written to `target/tmp/test-logs/<test>/<name>.stats`. The plugin
  counts inline under normal (fast) TCG, so even the long `fannkuch_v2` boot
  (hundreds of millions of instructions) gets an exact count - and observes only,
  so it never perturbs the pinned serial output or fault counts. `ensure_plugin`
  provisions it once per QEMU flavour in WSL: it downloads the (glib-free v8.2.2)
  `qemu-plugin.h`, builds a `.so` for each candidate plugin API version, and
  probes which version the local QEMU accepts (Debian's QEMU 8.2.2 wants **v1**
  for system emulation but **v2** for user mode), caching the chosen `.so` and
  its path under `target/qemu-plugin/`. If the plugin cannot be built/loaded (no
  WSL `gcc`, no network for the header, an unsupported QEMU - or `FORMAL_NO_PLUGIN`
  is set), the boot still runs and the stats are simply absent (a short run then
  falls back to `-d exec` line counting for the instruction total). The website's
  "Hello World!"/fannkuch-redux figures are produced by the dedicated
  comparison pipeline ([§6.1](#61-the-language-comparison-metrics-pipeline-testscomparisons)),
  which measures with the same plugin under controlled conditions and commits
  the results to `tests/comparisons/metrics.prom`.
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
  (`arr[i]` as `&arr + i*4`, then `p[0]`) -- the point of adding multiply +
  register-register add; writes/reads `arr[1]` and `arr[3]` at computed addresses
  and proves their sum. The element access at the end of the address arithmetic
  is what a `[u32]` pointee makes free: element 0 of a uniform-width pointee is
  the same offset and width wherever the pointer sits.
- `element_inference` ([tests/element_inference/](tests/element_inference/)):
  element indexing an **inferred** variable. `t0[0]` states no width, so the
  access is as wide as the type inference settles on, and inference settles on
  the narrowest type under which the program is *provable*: storing 300 and
  proving it reads back rejects `u8`/`i8` (they truncate it to 44, so the
  `require` fails) and lands on `u16`, emitted as `sh`/`lhu` over 2 bytes of
  `.bss` (the load unsigned, because the element's type says so). Pins the
  inferred configuration and the `accessed` union, which still carries the
  rejected `u8` candidate's byte while the lowering does not; boots and exits 0.
  The contrast with `inferred_widening` is deliberate: there a byte slice tells
  the verifier the width up front.
- `element_mixed` ([tests/element_mixed/](tests/element_mixed/)): a **mixed-shape**
  list, `[u8*2, i16*1, u32*1, i32*1]`, whose five elements sit at bytes 0, 1, 2,
  4 and 8. Which element `k` names depends on where the pointer sits, so the
  resolution walks the type from the pointer's exact offset instead of
  multiplying by a stride, and it carries each element's *type*, so the loads
  come out `lbu`/`lh`/`lwu`/`lw`: 200 stored in the `u8` reads back as 200 and
  not as the -56 a sign-extending load would give, and the signed elements keep
  their negatives. The `require`s prove that of the model and the boot proves it
  of the machine. Its emitted layout is also the compaction case: the unread
  second `u8` is removed, so every later element's immediate is re-pointed.
- `element_refusals` ([tests/element_refusals/](tests/element_refusals/)): the
  two ways an element index is refused. `out_of_bounds.hl` indexes past the end
  of a two-element array (`Invalid`, the element-granular form of an access past
  a label); `raw_address.hl` indexes a raw `#@` address, which has no element
  type to count (a `CompilerError::Unsupported` naming the byte-slice form to
  use instead). Neither executes.
- `sieve` ([tests/sieve/](tests/sieve/)): the Sieve of Eratosthenes counting the
  primes below 30, with the count (10) **proven** by the closing `require`. A
  small real program -- a `[u8]` flag array cleared then crossed out over
  concrete indices, nested `while` loops, `if flags[i] == 0` -- so the `Valid`
  outcome is a compile-time proof the sieve is correct; exercises the verifier's
  byte-array model and the `bge`/`bnez` branch resolution, then boots under
  `qemu-riscv64`. (Note it clears the array first: a fresh `thread` array reads
  as *any* value to the verifier -- only `global`s are modelled zero-initialised
  -- so reading an uncleared cell would make `if flags[i] == 0` indeterminate.)
- `bubble_sort` ([tests/bubble_sort/](tests/bubble_sort/)): bubble sort of a
  six-element `[u32]` array whose **sortedness is proven** -- after the sort the
  program `require`s `arr[k] <= arr[k+1]` for every adjacent pair, so `Valid`
  proves the array came out sorted. Exercises computed indexing (`&arr + k*4`,
  i.e. `mul`/`add`), u32 loads/stores at offsets 0 and 4, and `bge` over values
  loaded from memory; boots and exits 0.
- `collatz` ([tests/collatz/](tests/collatz/)): the Collatz step count from 7
  (16 steps) proven at compile time. Combines register-register `div`/`mul`/`rem`
  with the `if n % 2 == 0` zero-test branches (`bnez`/`beqz` on the `rem` result)
  the `reg_*` tests do not reach; boots and exits 0.
- `sentinel_sum` ([tests/sentinel_sum/](tests/sentinel_sum/)): sums and counts a
  zero-terminated `[u32]` array with a **data-driven** loop (`while *p != 0`),
  the sentinel-terminated iteration pattern the counted-loop programs do not use;
  `require`s the sum (23) and count (6), so loop termination on the sentinel is
  part of the proof. Covers the `beqz`-on-u32 loop-exit resolution over a value
  loaded from memory; boots and exits 0.
- `inferred_widening` ([tests/inferred_widening/](tests/inferred_widening/)):
  type inference of a `global _` declared **after** some computation. The 4-byte
  store rejects every type narrower than 4 bytes, and because the variable is
  introduced mid-program each rejected candidate backtracks through its
  *mid-program* first encounter (`invalid_path`'s re-attach-after-the-predecessor
  arm, which the inference tests that declare their variable first never reach);
  the search lands on `u32` (asserted). Boots and exits 0. It keeps the raw
  byte-slice form deliberately: stating the width is what drives this search
  (see `element_inference` for the same variable indexed by element).
- `gcd` ([tests/gcd/](tests/gcd/)): Euclid's algorithm, `require gcd(48,36) == 12`
  -- a `while b != 0` remainder loop whose result feeds back as the next divisor.
- `binary_search` ([tests/binary_search/](tests/binary_search/)): searches the
  sorted `[1 3 5 7 9 11]` for 7 and `require`s it is found at index 3, exercising
  computed indexing, the `(lo+hi)/2` divide, and the three-way comparison of a
  loaded `u32` against the target.
- `signed_bytes` / `signed_words` ([tests/signed_bytes/](tests/signed_bytes/),
  [tests/signed_words/](tests/signed_words/)): signed `i8` / `i32` arithmetic
  with negative values -- store a few negatives into an `[i8]`/`[i32]` array, read
  them back and prove the sum. These are the programs that drive the signed
  value-model arms ([§9](#9-conventions--gotchas) "Mixed-width integer arms").
- `signed_max` ([tests/signed_max/](tests/signed_max/)): `max([-5 3 -1 -8 2]) == 3`,
  whose running `if nums[i] > max` exercises signed `i32` comparison of values
  loaded from memory.
- `dot_product` ([tests/dot_product/](tests/dot_product/)): `[-1 2 -3] . [4 -5 6] == -32`,
  exercising signed `i32` multiply.
- `difference_array` ([tests/difference_array/](tests/difference_array/)):
  `diff[i] = arr[i+1] - arr[i]` over `[10 7 12 4]`, whose telescoping sum equals
  `arr[3]-arr[0] = -6` (asserted) -- a standard technique exercising signed `i32`
  subtract.
- `count_zeros` ([tests/count_zeros/](tests/count_zeros/)): counts the zero
  elements of `[3 0 5 0 0 2]` (= 3); each `if arr[i] == 0` branches (`bnez`) on a
  loaded `u32`, the branch-on-loaded-value path the `while != 0` sentinel
  (`beqz`) loop does not reach.
- `halfword_sum` / `signed_halfwords`
  ([tests/halfword_sum/](tests/halfword_sum/),
  [tests/signed_halfwords/](tests/signed_halfwords/)): 16-bit (`u16`/`i16`)
  arithmetic via the 2-byte `sh`/`lh` instructions -- store a few values into a
  `[u16]`/`[i16]` array and prove the sum. The programs that exercise the 2-byte
  access width and the `u16`/`i16` value-model paths.
- `int_output` ([tests/int_output/](tests/int_output/)): integer printing by
  digit extraction (`/10`/`%10` into a buffer, ASCII, `write`); prints `42`.
- `print_zero` ([tests/print_zero/](tests/print_zero/)): `print(0)` writes a
  single `0`. The integer arm peels digits with a loop a zero argument never
  enters, so before `print` laid a zero digit down explicitly the call wrote an
  empty slice. Prints `0 42 0`, and its `dialect.s` pins the inlined expansion,
  so a change to `print` shows up here first.

The five **LeetCode kernels** below were chosen to cover the algorithm families
the rest of the catalogue does not reach (hashing, two pointers, graph
traversal, dynamic programming, interval sweeping); `binary_search`,
`bubble_sort`, `sieve` and `difference_array` already cover binary search,
sorting, number theory and prefix arrays. Each runs over a small fixed input
and ends in a `require` on the known answer, so a `Valid` outcome IS the proof,
and each prints its answer so the language-comparison panels ([§6.1](#61-the-language-comparison-metrics-pipeline))
can hold every language to the same output.

- `two_sum` ([tests/two_sum/](tests/two_sum/)): Two Sum over `[2 7 11 15]` with
  target 9, `require`ing both indices of the answer (0, 1). The optimal O(n)
  solution, the hash map: `std` has no map, so the table is the honest
  open-addressing one, three parallel arrays with linear probing and a capacity
  of 8 for 4 keys. Two things make it the test that earns its keep: the
  complement `target - nums[i]` goes negative here, so every slot is the
  canonical non-negative remainder `((k % cap) + cap) % cap` (`rem` takes the
  dividend's sign, so a bare `%` would index the table backwards); and it
  indexes a table by a value **loaded out of memory**, which is what the
  pointer arithmetic in [§4.4](#44-symbolic-value--memory-model-srcverifier_typesrs)
  had to be generalised for. It also prints index `0`, so it covers
  `print_zero`'s arm end to end.
- `trapping_rain` ([tests/trapping_rain/](tests/trapping_rain/)): Trapping Rain
  Water over `[0 1 0 2 1 0 1 3 2 1 2 1]`, `require`ing the total of 6. Two
  pointers closing in from both ends with a running maximum on each side. The
  clearest example of the **complementary-`if` idiom** that stands in for the
  `else` the language does not have: `if t2 >= a4:` then `if t2 < a4:`, safe in
  that order because the first arm leaves the two equal.
- `coin_change` ([tests/coin_change/](tests/coin_change/)): Coin Change over
  coins `[1 2 5]` and amount 11, `require`ing the optimum of 3. An
  unbounded-knapsack table relaxed once per coin, with 99 standing in for
  "unreachable" (a plain number, so a candidate built from it stays in range and
  never wins a comparison). The inner loop starts at `v = coin`, so `v - coin`
  never wraps.
- `num_islands` ([tests/num_islands/](tests/num_islands/)): Number of Islands
  over a 4x5 grid, `require`ing the count of 3. There is no recursion (a `def`
  is inlined, so it cannot call itself), so the flood fill carries an explicit
  stack; a cell is sunk as it is pushed, so no cell is ever queued twice and the
  array cannot overflow. Its neighbour visit is a **program-local `def`** inlined
  at four call sites, the one test that shows a `def` outside `std`. The grid is
  written in full rather than relying on a zero fill, for the same reason `sieve`
  clears its flags.
- `merge_intervals` ([tests/merge_intervals/](tests/merge_intervals/)): Merge
  Intervals over `[[2 6] [1 3] [15 18] [8 10]]`, `require`ing the count and all
  three merged pairs. Two parallel arrays swapped in lockstep by the same bubble
  sort as `bubble_sort`, then one sweep whose correctness rests on the sort's
  ordering invariant. Its print loop is the worked example of surviving `print`'s
  register clobbers: the count and cursor move to registers `print` leaves alone.
- `print_poly` ([tests/print_poly/](tests/print_poly/)): the **polymorphic
  `print`** -- `print("Hi ")` + `print(42)` + `print(7)` -> `Hi 427`, the string
  arm and the integer arm of one `print` selected by the compile-time `if typeof`
  dispatch (and two integer prints exercising body-local-label hygiene). Asserts
  no directive leaks into the binary.
- `runtime_input` ([tests/runtime_input/](tests/runtime_input/)): a value the
  verifier cannot see, via `forget` -- it proves `arr[((a0 % 4) + 4) % 4]` in
  bounds for *every* `a0` while the runtime keeps `a0 = 12`. The double-rem is
  load-bearing: RISC-V `rem` takes the dividend's sign, so a single `% 4` on a
  havoced value spans `-3..3` (the interval transfer in `rem_by_constant`,
  [src/verifier_types.rs](src/verifier_types.rs), models exactly this), and
  only the `((i % d) + d) % d` canonical form narrows to `0..3`.
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
- `fannkuch_v2` ([tests/fannkuch_v2/](tests/fannkuch_v2/)): **V2** -- the *optimal*
  parallel fannkuch: 2 harts genuinely **share** the work (not a leader/worker
  split), each computing a disjoint set of permutation blocks into its OWN
  thread-local `perm`/`work`/`cnt`. The n! permutations split into n blocks by the
  top odometer digit; hart h takes blocks h, h+2, ...; because (n-1)! is even for
  n >= 3 every block starts at global parity 0, so the per-hart partial checksums
  simply add. The partials combine **lock-free**: `amoadd` into per-rank checksum
  slots, `amomax` into a shared max word. `n` is read at runtime = **12**
  (verifier-blind via `forget`, narrowed to 3 by `assume`); the arrays are
  full-12-initialised so dead-data compaction keeps them sized for the runtime n
  (the flip count also addresses `&work + k*4` directly, no O(k) walk). Verified for
  **2 harts** (3 is infeasible -- the interleaving search exceeds the step budget);
  booted under round-robin TCG (sequentially consistent, matching the verifier's
  model), the UART receives `3968050\nPfannkuchen(12) = 65` -- the same answer as the
  serial C reference, with the work split across two harts, then writes the
  `sifive_test` finisher to halt cleanly. **`#[ignore]`d** (~2 min under bare-metal
  QEMU; run with `--run-ignored`). Making this the optimal shape rather than
  leader/worker required several compiler/verifier updates -- see **parallel-program
  obstacles** in [§9](#9-conventions--gotchas).
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
- `tls_probe` ([tests/tls_probe/](tests/tls_probe/)): per-hart thread-local storage
  end to end. Two harts each store a distinct value (`rank + 1`) in a `thread`
  variable, read it back, and combine (`1 + 2 = 3`) -- which only holds if codegen
  gives each hart its own copy. The runtime check behind the per-hart TLS lowering
  ([§4.8](#48-code-generation--emit_executable-srccodegenrs)).
- `vector_add` ([tests/vector_add/](tests/vector_add/)): a SIMD vector add via the
  RISC-V **V (vector) extension** (register-only subset). `vsetivli` sets vl = 4,
  `vmv.v.i` splats 1 and 2 into `v0`/`v1`, `vadd.vv` adds lane-wise into `v2`,
  `vmv.x.s` extracts lane 0 (= 3). The verifier models a vector register as a
  `MemoryValue::List` of lanes and `vl` as a tracked register, computing the
  lane-wise add concretely; the program is assembled with `-march=rv64gcv` and run
  under `qemu-riscv64` (which enables V by default), printing `3`. (Vector
  loads/stores and `vrgather` -- the SIMD pancake-flip primitive -- are a further
  step toward a vectorised fannkuch.)
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

- `hl_types` ([tests/hl_types/](tests/hl_types/)): the run-length list-type
  grammar -- comma-separated runs (`[u8*3]`, `[u8*2, u16*2, u8*3]`, runs mixed
  with plain elements), the legacy outer `*n` cycling suffix, and the
  `[u8]*13` == `[u8*13]` equivalence -- pinned as exact `#$` dialect lines
  (every form expands to the same flat space-separated list, which is why no
  other test's pins move). The rejection paths (spaced `u8 * 3`, zero and
  non-numeric counts, missing or unknown run element) live in
  `translate_errors`.
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
- `partial_variable_access`: accesses only elements 0 and 2 of a `[u8*4]`;
  `accessed` records exactly `(0,1)`/`(2,3)` and `.bss` compacts to those two
  bytes, the byte-2 access re-pointed to offset 1. 14 steps; boots.
- `descriptor_read_union`: hart 0 reads a descriptor's type-number, hart 1 its
  length; `accessed` is the union, so both fields are emitted (back to back:
  the unread field between them is removed and the length read re-pointed
  16 → 8) plus an empty subtypes array. The two reads are exclusive `if`
  blocks (`if t0 == 0:` / `if t0 != 0:`). 46 steps; boots.
- `locality_runtime_read` (the inverse of the elision rule): `lb` of the
  locality byte (offset 24) at runtime keeps the `.byte 1`; as the _only_
  emitted descriptor byte, the read re-pointed to offset 0. Runs **hosted**
  (`run_linux`, which has no no-`.byte` assert) and exits 0; 7 steps.
- `offset_widened_inference`: a 4-byte store at offset 2 forces the type
  search through `u8…i32` to `u64` (the offset participates in inference);
  `accessed` is exactly `(2, 6)`. 32 steps; runs **hosted** (`run_linux`).
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

### 6.1 The language-comparison metrics pipeline ([tests/comparisons/](tests/comparisons/))

The website's "same program, side by side" panels (index.html) are backed by
**measured, committed data**, not hand-typed numbers. The pieces:

- The **programs** are the `PROGRAMS` table in
  [tests/comparisons/support.rs](tests/comparisons/support.rs): `hello`, the
  five LeetCode kernels `two_sum`/`rain`/`coins`/`islands`/`intervals`
  ([§6](#6-integration-tests-tests)), and `fannkuch`. Everything that differs
  between them (the test folder formal builds, its hart count, the Ada build
  flags, the run timeouts, the output every language must produce, whether the
  runtime runs are heavy enough to gate) is a field of that row, so adding a
  program is one row rather than an edit in six `match` arms.
- [tests/comparisons/programs/](tests/comparisons/programs/): the Rust/C/C++/
  Zig/Ada source for each program, verbatim the code the page displays
  (the page reads these files, see [§6.3](#63-the-website-indexhtml)). Every
  language runs the **same algorithm and the same data structure**: the
  section is titled "the same program, every language", so `two_sum` is the
  same hand-rolled open-addressing table in all six, not `HashMap` in Rust and
  `unordered_map` in C++. Reaching for each language's standard map would
  measure library choice, which is a different (and worth having, separately)
  comparison from the one this section makes.
- [tests/comparisons/main.rs](tests/comparisons/main.rs): the `comparisons`
  test (**`#[ignore]`d**; run it with
  `cargo nextest run --run-ignored all comparisons`). For each program x
  language it builds a **static RISC-V Linux (musl) binary** with a pinned
  toolchain - formal via the in-process pipeline + `as`/`ld`; Rust via the
  pinned nightly (`FORMAL_RUST_TOOLCHAIN`, default `nightly`) with
  `-Zbuild-std` and self-contained `rust-lld`; C/C++ via clang (`zig cc` /
  `zig c++`, path override `FORMAL_ZIG`); Zig via `zig build-exe`; Ada via
  host `gnatmake` (static-only: no RISC-V Ada toolchain) - and measures:
  **compile time** (cold output dir, warm toolchain caches; formal's includes
  verification), **static instructions** (formal: emitted-assembly lines, the
  page's `grep -cE '^    [a-z]'`; others: RISC-V `objdump` of the stripped
  binary), **binary bytes** (stripped), and, running under user-mode
  `qemu-riscv64` with an **empty guest environment** (`env -i`, fixed
  `./prog.elf` argv, so counts are reproducible): **instructions executed** and
  **peak memory working set** from an instrumented (`formal_stats` plugin) run
  plus **execution time** from a plugin-free run (best of 3 for `hello`).
  Requires a **plugin-enabled** `qemu-riscv64` (Ubuntu's `qemu-user` package
  is built without `--enable-plugins`; the workflow builds QEMU from source).
- [tests/comparisons/metrics.prom](tests/comparisons/metrics.prom): the
  results, Prometheus text format, one gauge per metric labelled
  `{program,language,origin}` plus a `formal_comparison_environment_info`
  metric whose labels record the exact environment (qemu/binutils/rustc/zig/
  gnat versions, host, OS). **Committed but generated**, like `Cargo.lock`.
- The page: index.html's `COMPARISON-DATA` block (the `METRICS` object and the
  execution-time tooltip's environment strings) is **generated from the
  metrics file**; `cargo run --example update_website` re-injects it without
  re-measuring, and the static (no-JS) numbers in the panel bodies are synced
  too. The shared parse/render/inject code is
  [tests/comparisons/support.rs](tests/comparisons/support.rs).

Modes (mirroring the suite's `BLESS` convention):

- **Check** (default): re-measures every language whose pinned toolchain is
  installed *at the recorded version* (a differing version skips with a
  warning - measuring under a different compiler is drift, not regression -
  or fails under `FORMAL_COMPARISONS_STRICT=1`, which CI sets) and asserts
  the deterministic metrics (static instructions, bytes, executed
  instructions, peak memory) **exactly reproduce** the committed file.
  Timings are informational (never compared); formal's 2-thread fannkuch
  runtime figures get a 10% tolerance (real scheduling nondeterminism);
  `origin="legacy"` values (imported from the pre-pipeline experiment) only
  warn until first blessed. Also asserts index.html is in sync with the file.
- **`BLESS=1`**: rewrites the measured entries (flipping them to
  `origin="measured"`), records the environment, and regenerates both the
  file and index.html.
- `FORMAL_COMPARISONS_FULL=1` adds the heavy **fannkuch runtime runs**
  (n = 12: minutes plugin-free, hours instrumented); otherwise fannkuch is
  built and measured statically and its committed runtime figures are left
  untouched. `FORMAL_COMPARISONS_LANGUAGES=<subset>` (comma-separated)
  restricts a run to those languages, e.g. re-blessing one language after a
  toolchain bump; `FORMAL_COMPARISONS_PROGRAMS=<subset>` does the same for
  programs. Both matter more than they did: a full run is now **7 programs x 6
  languages = 42 cells**, so measuring one new program is
  `FORMAL_COMPARISONS_PROGRAMS=two_sum` rather than a full sweep. The check
  that fires on a qualifying push to master pays the full 42 unless the
  workflow narrows it, which is the main recurring cost of adding a program.

A program can be added to the page **before** it is measured: the panels read
their code from the files, and the generated `METRICS` block simply carries no
row for it, so the page shows the sources and says "not measured yet" in place
of the figures. That is the intended staging, since a measure run is a
controlled-environment job (below) rather than something a contributor runs.

CI ([.github/workflows/comparisons.yml](.github/workflows/comparisons.yml))
installs the pinned toolchains (building a plugin-enabled `qemu-riscv64` from
source, cached), runs the check on pushes touching the pipeline, and offers a
`workflow_dispatch` **measure** mode (optionally **full**) that re-blesses and
commits `metrics.prom` + `index.html` - so the "re-measure" loop can run
entirely in the controlled CI environment.

### 6.2 The factory-default setup test ([tests/setup_e2e/](tests/setup_e2e/))

One **`#[ignore]`d** integration test proves the "setup is `cargo build`"
promise end to end, with no shims: it boots an **empty factory-default Linux
machine** as a local QEMU/KVM VM, performs the documented human steps (install
Rust, unpack this repository), runs `cargo build` over `ssh -tt` - a real
terminal, so setup's console prompts genuinely appear and a piped `y` answers
the reboot question - rides through the reboot when setup requests one, then
runs the **full test suite inside the guest**. Run it deliberately (it
downloads a cloud image once; about 3 minutes on a 24-core host):

```sh
cargo nextest run --run-ignored all -E 'test(factory_default_linux)'
```

- **Requirements fail loud.** The test probes its requirements up front
  (QEMU x86-64, `qemu-img`, `genisoimage`, the OpenSSH client, `curl`, KVM
  access; all driven through WSL on a Windows host, like the QEMU boot tests)
  and a missing one fails the test with the exact install command - no silent
  skipping.
- **What it asserts.** It boots the current Ubuntu LTS server cloud image
  (cached under `~/.cache/formal-e2e/images`; delete to refresh), asserts the
  first build reports real installs, handles the reboot + login-shell resume
  when the apt run requests one, builds `--features hpc` (which provisions
  libclang), asserts a re-run build is **silent** (setup complete +
  idempotent), asserts every dependency probe passes, and runs
  `cargo nextest run` inside. Works on a Linux host or through WSL2 (Windows
  11 enables the needed nested virtualisation for WSL2 by default), and on
  GitHub's standard Linux runners (they expose `/dev/kvm`); CI
  ([.github/workflows/setup-e2e.yml](.github/workflows/setup-e2e.yml)) runs
  it weekly and on demand.
- **Recursion guard.** Every in-guest command sets `FORMAL_E2E_INNER=1` and
  the test fails immediately (loudly, never a silent green skip) under it, so
  the suite running inside the guest cannot boot a VM inside the VM
  (`#[ignore]` already keeps it out of the guest's plain `cargo nextest run`).
- **Observability.** Live progress streams to
  `target/tmp/test-logs/<test>/e2e.progress`; every driver command is logged
  to `driver.log`, the guest console to `serial.log`, and each long phase
  (prep, builds, suite) to its own tail-able `.log`. The guest exposes VNC on
  loopback port `5948` - snapshot with `vncsnapshot 127.0.0.1:48` in WSL when
  a phase looks stuck.

**The removed Windows sibling (Aug 2026).** A `factory_default_windows` test
and its unattended Server-image recipe lived at `tests/setup_e2e/windows/`
and proved setup's whole Windows flow on a real factory guest: WSL detection,
the direct `wsl --install` (no UAC ceremony with an admin token; its exit
code is nonzero even on success, hence build.rs's feature-state check), the
`[y/N]` prompt over ConPTY, RunOnce scheduling, the reboot, and the resumed
build. It was removed because the platform cannot finish the job: WSL2
inside a guest needs the guest to boot its own hypervisor, which never
completes above KVM-inside-WSL2-inside-Hyper-V on a Windows host (measured:
all vCPUs pegged 27+ minutes), Windows Server 2022 is WSL1-only with imports
that wedge, hosted CI runners offer no nested virtualisation, and a
Linux/KVM box was not available. If such a box materialises, recover
everything with `git log -- tests/setup_e2e/windows` (the recipe, the
autounattend answer file, the import ladder, and the per-platform findings
are all in those commit messages and DEVELOPMENT.md revisions).

### 6.3 The website ([index.html](index.html))

One hand-written static file: no build step, no framework, no npm package.
Everything except the fonts and the syntax highlighter is inline. It is styled
after [mojolang.org](https://mojolang.org/), and the parts of that style worth
knowing before editing it are:

- **Dark-first, one accent.** Every colour is a custom property: the light
  values sit on bare `:root`, and `[data-theme="dark"]` redefines the same
  names. The single accent is `#ff552a`, with the gradient
  `linear-gradient(105deg, #fd2b01 5%, #ed810c 100%)` on the primary buttons.
  The accent is allowed on the status strip, the buttons, the section icons,
  the code-panel hairline and the `#$ #& #@ #! #?` directives, and nowhere
  else.
- **Hairlines, never elevation.** Cards are a `0.5px` border and a `2px`
  radius on a transparent fill, with `box-shadow: none`. Depth comes from
  surfaces one step darker or lighter than their parent (nav `#111`, page
  `#1a1a1a`, code panel `#292828` in dark), not from shadows.
- **Two weights, six sizes.** Inter at 400 and 500 only, at 48/32/18/16/14/12
  px, with negative tracking that grows with size. Roboto Mono at 12px inside
  the panels. Section headings are centred with nothing above them; everything
  under a heading is left-aligned.
- **Backgrounds break out, content does not.** Coloured bands span the
  viewport; their content stays in the 60rem container, and long prose narrows
  to 37.5rem.

**The machine-written parts.** The comparison section's DOM is written by
[tests/comparisons/support.rs](tests/comparisons/support.rs) as raw text, not
through a DOM parser, so a redesign has to preserve its exact shape (§6.1):

| Thing                                                    | Rule                                                                      |
| -------------------------------------------------------- | ------------------------------------------------------------------------- |
| `// COMPARISON-DATA-BEGIN` / `-END`                      | JavaScript line comments, once each, in order, inline in `index.html`     |
| `// COMPARISON-SOURCES-BEGIN` / `-END`                   | the same, for the generated panel sources                                 |
| The generated block's indentation                        | 8 spaces; its `<script>` stays a direct child of `<body>`, one brace deep |
| The three `// prettier-ignore` lines                     | kept, or prettier and the generator rewrite each other forever            |
| `formal-{compile,count,bytes,exec,mem,time}` and `lang-` | one `id="name"` each, on an inline `<b>`, value as the whole text node    |
| The static defaults                                      | the `hello` program, `formal` left and `rust` right, matching the tabs    |
| `.compare pre.asm` with `#lang-code` its direct child    | the height equaliser measures `parentElement.scrollHeight`                |
| The `*-wrap` spans                                       | each encloses its own leading `<br />`, so hiding it hides the break      |

**The three selectors.** The comparison carries three tab groups, each a
`.tabs` row of equal-width buttons sitting over the panel it drives:
`.prog-tabs` spans the section and swaps both columns, `.level-tabs` sits over
the left column and switches the formal panel between the surface source and
the RISC-V dialect the verifier proves, and `.lang-tabs` sits over the right
column and swaps the language. The selected tab is marked by
`aria-selected="true"` and nothing else, so the CSS indicator and the script's
state cannot disagree. The panels carry no name headers: the selectors already
say what is shown.

**The panel sources are generated, not copied.** Every panel's code comes from
the file the pipeline actually measures, spliced into the page's
`// COMPARISON-SOURCES-BEGIN` / `-END` block by `read_sources` +
`render_sources_block` ([tests/comparisons/support.rs](tests/comparisons/support.rs)):
`formal`'s two levels from the test's `input.hl` and `dialect.s`, the other
five languages from `tests/comparisons/programs/<program>.<ext>`. They cannot
drift, because the same `git diff --exit-code index.html` that guards the
numbers now guards the sources, and `cargo run --example update_website`
re-splices both. The formal panel's source has its **header comment stripped**
(the leading run of `#` lines): a test's header says what the program proves
and maps its registers, which is documentation of the test, and the reference
implementations carry no header at all, so leaving it in would make the panels
incomparable in exactly the dimension the section is about. Inline comments
stay. The only hand-written strings left in a panel are the reproduction
commands, which are not a file anywhere.

The end-to-end section still copies `tests/uart_hello/` by hand, and nothing
checks that one; the same treatment would fix it.

**Syntax highlighting.** Prism arrives as one pinned, integrity-checked
request to jsDelivr's `combine` endpoint (core plus the `clike`, `c`, `cpp`,
`rust`, `zig` and `ada` grammars, 19 KB). The `formal`, RISC-V and shell
grammars are defined inline; the RISC-V one gives the five directives their
own `annotation` token, which is the reason to highlight the assembly at all.
Rules that keep it safe and cheap:

- Panels paint through `window.paintCode(el, text, lang)`, which sets
  `textContent` first and only then highlights. Source text is never
  interpreted as markup.
- If the request fails (offline, blocked, or an integrity mismatch after a
  version bump) `window.Prism` is undefined, `paintCode` degrades to a plain
  `textContent` write, and the panels keep their background, border and
  monospace font. Re-derive the hash with
  `curl -sL <url> | openssl dgst -sha384 -binary | openssl base64 -A` after
  changing the pinned version.
- `equalizeHeights` measures with plain `textContent`. Highlighting inside its
  six-language measurement loop would tokenise a fannkuch-sized source on
  every resize tick.

**After editing**, in this order (prettier first: it normalises the line
endings the generator assumes):

```sh
npx prettier ./index.html --write
cargo run --example update_website   # must print "already in sync"
git diff --exit-code index.html
```

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
  libclang (provisioned by `build.rs` alongside MPI), so it builds/runs
  on Linux / under WSL (see [`deploy/`](deploy/) for the k8s + Kubeflow MPI
  Operator target). The remaining work is purely a *scheduling* upgrade -
  replacing the per-wave barrier with lifeline work-stealing + Mattern
  termination detection for better load balance at scale; the transport and the
  reduce are done.

**How a verification executes** - the same exploration, exposed through five
backends that all produce the identical outputs:

| Backend                 | Entry point                                                          | Parallelism                     |
| ----------------------- | -------------------------------------------------------------------- | ------------------------------- |
| Sequential oracle       | `Explorerer::next_step`                                              | none (the reference)            |
| Fixed-config            | `verify_configuration` / `verify_configuration_pooled`               | none                            |
| In-process pool         | `verify_configuration_parallel` / `verify_sweep` / `verify_inferred` | rayon (all cores)               |
| Distributed simulation  | `verify_configuration_distributed_sim`                               | rayon + serialize round-trip    |
| Real MPI, wave          | `outer_sweep_winner` + `verify_configuration_mpi`                    | `mpirun -n N`, barrier per wave |
| Real MPI, work-stealing | `verify_configuration_mpi_stealing`                                  | `mpirun -n N`, barrier-free     |

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

- `TranslateError` ([hl.rs:41](src/hl.rs#L41)): `{ line, message }` for an `hl`
  translation failure (1-based line; `translate` never panics).
- `AstNode` / `AstValue` / `Span` ([ast.rs:7](src/ast.rs#L7)): intrusive AST
  list node, value, source span.
- `Instruction` ([ast.rs:177](src/ast.rs#L177)): 27-variant tagged union of
  supported instructions/directives (incl. `ecall`).
- `Region` / `RegionBound` / `RegionPermissions` ([ast.rs](src/ast.rs)): the
  `#@` directive: region bounds (immediate/register) + `r`/`w`/`rw`.
- `Type` / `FlatType` / `Locality` ([ast.rs:335](src/ast.rs#L335) /
  [276](src/ast.rs#L279) / [313](src/ast.rs#L316)): compile-time types;
  `FlatType` is the runtime type-number encoding.
- `Explorerer` ([verifier.rs:150](src/verifier.rs#L150)): the verification
  state machine.
- `VerifierNode` / `VerifierLeafNode` ([verifier.rs:114](src/verifier.rs#L114)
  / [99](src/verifier.rs#L131)): execution-tree interior / frontier nodes.
- `ExplorePathResult` ([verifier.rs:1708](src/verifier.rs#L1708)): `Valid` /
  `Invalid` / `Continue(self)`.
- `ValidPathResult` ([verifier.rs:1770](src/verifier.rs#L1770)):
  `{ configuration, touched, jumped, accessed, transitions, uncompactable,
  pinned_nodes }`; feeds the optimizer + codegen.
- `AccessedRanges` ([verifier_types.rs](src/verifier_types.rs)):
  `BTreeMap<Label, BTreeSet<(u64, u64)>>`: runtime-accessed bytes per region;
  drives dead-data elimination.
- `AccessTransitions` ([verifier_types.rs](src/verifier_types.rs)): per-node
  `(label, from, to)` pointer transitions; drives layout compaction's
  instruction rewriting.
- `InnerVerifierConfiguration` / `Section` / `Permissions`
  ([verifier.rs:71](src/verifier.rs#L71) / [46](src/verifier.rs#L77) /
  [53](src/verifier.rs#L84)): per-system input: harts + memory map.
- `MemoryValue` ([verifier_types.rs:660](src/verifier_types.rs#L660)):
  universal symbolic value (ranges / list / ptr / csr).
- `MemoryLabel` / `MemoryPtr`
  ([verifier_types.rs:1235](src/verifier_types.rs#L1235) /
  [1189](src/verifier_types.rs#L1188)): label-tagged symbolic memory &
  pointers.
- `State` / `MemoryMap` / `RegisterValues`
  ([verifier_types.rs:1554](src/verifier_types.rs#L1554) /
  [1260](src/verifier_types.rs#L1259) / [1552](src/verifier_types.rs#L1680)):
  reconstructed machine state.
- `TypeConfiguration` / `LabelLocality`
  ([verifier_types.rs:1726](src/verifier_types.rs#L1726) /
  [1573](src/verifier_types.rs#L1702)): inferred per-variable type+locality;
  the proof output.

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
  back past the whole stretch. (`fannkuch_v2` was originally this leader/worker
  shape; it is now a real 2-hart parallel program -- both harts advance, so the
  front-search is cheaper -- but its 2-hart verification is still ~3.5M steps and
  3 harts is infeasible; see **parallel-program obstacles** above.) The debug-only
  loop backstop is generous (1e9) rather than tight so
  the legitimate deep walk does not trip it; the real guard is the "reached root"
  check. A cached/incremental front map would remove the O(N²) (future work, part
  of the parallel rework).
- **Dead-data compaction sizes arrays to the _verified_ `n`.** Codegen sizes each
  variable's `.bss` storage to the bytes the verifier saw accessed (it removes
  dead gaps too, keeping `.zero` padding only below the last live byte;
  [§4.8](#48-code-generation--emit_executable-srccodegenrs)). So with
  `forget`+`assume` narrowing the verifier to a small `n`, an array initialised
  over `0..n` is emitted at that small size -- and a **larger runtime `n`** then
  reads past it, producing invalid permutations whose flip loop never terminates
  (the bug behind every early `fannkuch_v2` runtime failure). Fix: initialise the
  arrays over the full **runtime** range with a *literal* bound (e.g. `0..12`, not
  `0..n`), so every element is live and the array stays full-sized. `fannkuch_v2`
  does this to run n = 12 while verifying n = 3.
- **Parallel-program obstacles (and how the compiler/verifier was updated).**
  Making `fannkuch_v2` a *real* parallel work-sharing program (rather than the
  leader/worker shape, where only one hart computes) surfaced a series of
  limitations. Each was fixed so the optimal algorithm is expressible; the lessons
  generalise to any concurrent-multi-hart program:
  1. **Thread-local storage was single-hart in codegen.** The verifier models each
     `thread` variable as a distinct copy per (contiguous) hart index, but codegen
     emitted one fixed-address copy. With two harts running concurrently they
     clobbered each other's `perm`/`work`/`cnt`, producing invalid permutations
     whose flip loop never terminates (the program hung). *Fix:* per-hart TLS in
     codegen -- N copies + a boot prologue setting `tp = mhartid * block_size`, each
     `la` of a thread-local adding `tp`
     ([§4.8](#48-code-generation--emit_executable-srccodegenrs); `tls_probe` pins it).
     Inert for single-hart / leader-worker programs.
  2. **The verify-small/run-large hazard hits branches, not just arrays.**
     `remove_branches` drops a branch direction not taken during verification. The
     parallel max combine `if mf[1] > mf[0]` is never taken at the verified n
     (where the two harts' partials are *equal*), so the body the runtime n needs
     was pruned -- the max came out wrong while the checksum was exact. *Fix:* use
     an **atomic max** (`amomax`) -- a single instruction with no branch to prune --
     for the reduction; more generally, reduce lock-free with atomics (`amoadd` for
     the sum, `amomax` for the max) rather than a compare-and-select the verifier
     can specialise away. (`forget`ting the operands does *not* work: the verifier
     errors on an indeterminate `bge` rather than forking -- a candidate future
     improvement.)
  3. **3-hart verification is infeasible.** The interleaving search for 3 harts
     exceeds the step budget (>1e7), so the parallel program is verified for **2
     harts**. The work-split (block stride) is written for 2.
  4. **The verifier assumes sequential consistency; the runtime must match.** The
     interleaving search is an SC model. Run the multi-hart program under
     **round-robin TCG** (single-threaded, SC), *not* MTTCG (`thread=multi`, weakly
     ordered): under MTTCG a verified cross-hart hand-off can observe a stale read
     that SC forbids. A `fence` instruction exists for the weak-memory case, but
     QEMU MTTCG did not reliably honour it here, so round-robin (SC) is the
     reference execution. (A verifier that models weak memory, or codegen that
     inserts the right fences, is future work -- it connects to the determinism
     guardrails in the HPC distributed-verifier plan.)
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
  - **Pointer plus an integer of any width.** `MemoryValue`'s `Add` carried one
    arm per pointer-and-width pair (`U8`, `I8`, `I64`) and sent every other
    width to the catch-all `todo!()`, so `&table + slot` where `slot` came out
    of memory **panicked the compiler**. It is now a single arm over any value
    `as_i64_range` accepts, in either operand order, going through one
    `offset_pointer` helper: a register is 64-bit, so the offset moves by the
    value's `i64` range whatever width it was loaded at. This is what indexing
    a table by a value read out of memory needs, which is to say what a hash
    table needs (`two_sum`). The replaced `I8` arm *subtracted* where it should
    have added; nothing exercised it, and the suite is unchanged by the fix.
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
    the generic `compare`). The **signed-memory** arms were filled the same way
    for the `signed_bytes`/`signed_words`/`signed_max`/`dot_product`/`difference_array`
    programs (each mirrors the existing `U8`/`U32` arm with signed semantics, so
    it only fires on the `i8`/`i32` paths the unsigned programs never reached):
    `set` gained `(I64,I8)`/`(I64,I32)` (interior + end-of-list, keeping the
    register's low bytes as `sb`/`sw` do); `Add` gained `(I8,I8)`/`(I64,I8)`/
    `(I32,I32)`/`(I64,I32)`/`(I32,I64)`; `Sub` and `Mul` gained `(I32,I32)`; and
    `compare` gained `(I32,I32)` (a plain omission next to `(I8,I8)`/`(I16,I16)`)
    plus the mixed `(I64,I32)`/`(I32,I64)` orderings. Each widens a loaded
    signed value to `I64` in the register file, matching RV64's sign-extending
    `lb`/`lw`. The 2-byte `lh`/`sh` later landed (`halfword_sum`/`signed_halfwords`),
    filling the matching `u16`/`i16` arms the same mirror way (`set`
    `(I64,U16)`/`(I64,I16)`, `Add` for the `U16`/`I16` pairs, and the
    `From<MemoryValueU16/I16> for MemoryValueI64` widenings). Element indexing
    then reached the arms no program had: a *scalar* variable of any width can
    now be written and read whole (`p[0]` of a scalar is the whole scalar,
    whatever type inference picks), so `MemoryValue::set`/`get` gained a
    whole-scalar fast path (`narrow_scalar` keeps the register's low
    native-endian bytes, and a value known only as a range havocs the slot, the
    sound over-approximation) and `compare` gained a generic fallback that
    compares any two scalars as `i64` ranges, subsuming the hand-written mixed
    pairs. The same class of gap will resurface for any new type pairing a
    future program exercises.
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
  the `name: <locality> <type>` define form: a raw slice store (`t0[0:4] = t1`)
  contains a `:` and would otherwise be taken for a definition. Preserve this
  order when adding statement forms (an element store, `t0[0] = t1`, has no
  colon, so the ambiguity is the raw form's alone). The surface language has **no `goto` and
  no bare labels** (control flow is `if`/`while` blocks plus `require`); the
  dialect's labels are generated (`_l0`, …).
- **An element access must resolve the same way on every path.** One `#[`/`#]`
  directive becomes one instruction, so the `(element type, offset)` recorded
  per node must be unanimous; a mixed-shape pointee reached at two different
  element boundaries has no single instruction to stand for it and is refused
  (codegen emits `.err`, failing the assembler, rather than picking one). This
  is also why the lowering record is pruned on backtracking rather than unioned
  like `accessed` ([§4.3](#43-verification--explorerer)).
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
- A pointer plus a **possibly-negative** offset range panics
  (`MemoryValueU64::try_from(...).unwrap()` in the `Ptr + I64` `Add` arm)
  instead of rejecting with a diagnostic: the old single-rem spelling
  (`forget a0; a1 = a0 % 4; t4 = a1 * 4; p = &arr + t4`) hits this since the
  signed-rem fix made `a1` span `[-3, 3]`. The double-rem idiom avoids it;
  the clean fix is a fallible pointer-add that rejects the path.
- **Element indexing is constant-index only.** `p[k]` needs a literal `k`: a
  runtime index (`arr[i]`) is refused by the front-end with the address
  arithmetic to write instead, because the affine expansion needs a scratch
  register and the language has not decided which one it may clobber
  ([§11](#11-design-notes--roadmap)). Two further refusals, both with a message
  naming the byte-slice form: indexing a **raw address** (no element type to
  count) and indexing a pointee whose elements are not scalars (a nested list,
  such as the descriptor *subtypes* array, whose element is a whole 25-byte
  record). An 8-byte element **store** is refused too: the dialect has no `sd`.
- Multi-element list slice **get** returns `ListMultiple` (unimplemented;
  `covers` is collected but never applied). **Set** now distinguishes: a
  **ranged** offset applies the sound flank-preserving weak update
  (`ranged_weak_update`, [src/verifier_types.rs](src/verifier_types.rs)):
  every scalar element the maximal span may touch havocs to its full type
  range ("old value or new value", the raw-section rule), elements outside
  the span keep their values, and a covered non-scalar is still
  `ListMultiple`. An **exact** offset that would cross element boundaries
  remains `ListMultiple`.
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

### Execution models: hosted Linux and bare-metal (parallel work streams)

The QEMU-booting tests run in one of two **execution streams**, advanced
independently over time:

- **Hosted Linux** (the default): the program is an ordinary Linux process,
  ending in `exit(0)` (a Linux `exit` `ecall`), output via `print` (`write`
  `ecall`). It builds to a static ELF and runs under **user-mode `qemu-riscv64`**
  (`run_linux`). This is cheap and representative, so it is where programs are
  **benchmarked**: the `formal_stats` TCG plugin reports instructions executed,
  the memory working set over time (percentiles + peak) and wall-clock time (§6).
  Most tests live here. A **multi-hart** program is hosted too, via
  `emit_executable_hosted` (§4.8): the harts run as real OS threads (spawned with
  `clone`), so they execute on separate cores under qemu-user MTTCG -- genuine
  parallelism. `fannkuch_v2` runs this way; dropping its racy UART MMIO for
  `print` also collapsed its verification from ~3.5M steps to ~24k (the MMIO
  stores were the racy interleaving explosion).
- **Bare-metal**: the program owns the machine, ends in `unreachable` (a `wfi`
  halt loop), and talks to hardware directly (UART MMIO, the `sifive_test`
  finisher). It runs under full-system **`qemu-system-riscv64 -machine virt`**
  (`run_program` / `run_program_smp`). This stream is for what hosted Linux cannot
  express: **MMIO devices** (`uart_hello`), **raw `#@` regions** (`heap_regions`,
  `mixed_pointer_raw`), programs that read the machine-mode **`mhartid`** CSR
  directly (`descriptor_read_union` via `csr(mhartid)`), the multi-hart racy
  exemplars and the distributed-model demo (`racy_*`, `tls_probe`,
  `parallel_probe`, `hpc_demo`), and the halt-terminal dead-data rule
  (`terminal_access`).

These are **separate work streams to advance over time**, not a one-time switch. A
program may exist in both: `uart_hello` (bare-metal UART) has the hosted
`linux_hello` as its counterpart. The migration direction is "**host what can be
hosted**" (so it gets cheap user-mode benchmarks + real parallelism) and "**keep
the rest bare-metal**". A program is hostable iff it uses no MMIO / raw address
and never reads `mhartid` directly; **multi-hart thread-local storage is no longer
a blocker** -- the hosted codegen's `clone` prologue gives each hart its own `tp`
(this is what moved `fannkuch_v2` to the hosted stream). `run_linux` **enforces**
hostability by failing on a guest crash (a stray `csrr mhartid` raises SIGILL in
user mode), so a non-hostable program cannot be migrated by mistake. Open future
work in the Linux stream: a hosted hart-id primitive so `mhartid`-reading programs
(`descriptor_read_union`) can move; `partial_variable_access` (multi-hart TLS, no
`mhartid`/MMIO) is now hostable and could move; and hosted variants of the racy /
MMIO programs.

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

### Typed indexing, ergonomics, and the cost contract (designed July 2026)

The goal sourcing all of this: simplify how users write code and bring the
surface closer to a **systems-programming dialect of Python**. Decisions made
(the run-length type syntax and constant-index element access below have
landed; the rest is the agreed direction):

- **The cost contract is a guiding principle, not a strict rule.**
  One-simple-statement-one-instruction stays the documented default, but a
  multi-instruction lowering is acceptable when its expansion is *fixed,
  documented, and visible in emitted output* (the string-literal `def`
  argument expansion set the precedent). Corollary worth writing into law: a
  register's **verifier-exactness must never become an emitted immediate**
  (only syntactic constants may); otherwise the `forget`+`assume`
  verify-small/run-large idiom bakes the small-`n` value into the binary,
  the same hazard `remove_branches` has for branches. The same hazard also
  permanently excludes comparison-tree lowerings for anything data-dependent:
  **all sugar lowerings must be branch-free**.
- **Run-length list types** (landed): `[u8*13]`, `[u8*2, u16*2, u8*3]`;
  comma-separated runs, `*` binding tightly, legacy `[t, t]*n` retained as
  cycling sugar ([§5.1](#51-the-hl-front-end)).
- **Indexing is a function on the list type, not pointer arithmetic** (landed
  for a constant index, [§5.1](#51-the-hl-front-end)). A
  constant index `x[k]` resolves to `(byte offset, element type)` and lowers to
  one sized load/store (the LLVM-GEP-struct / Wasm-`struct.get` model). It
  resolves in the *verifier* rather than at translate time as first sketched:
  the front-end is stateless and does not know what a register points at, and
  for an inferred variable the pointee's type is not a fact about the source at
  all but about the configuration being proven. Which turned out to be the
  better half of the bargain, since an access that states no width lets
  inference pick the narrowest type under which the program is **provable**
  (`element_inference`), and knowing the element's type lets the load extend
  the way the value was modelled (`lbu` vs `lb`). The **byte slice survives**
  as the raw form, for memory with no element type of its own; it is not a
  transitional spelling. A runtime index
  `x[i]` carries the implicit obligation `0 <= i < len(x)` **verified at
  compile time** (never a runtime check): interval containment at the access
  site, `check_load_at`'s byte-bounds check lifted to element granularity.
  Because types are static, `len` is a per-state constant, so intervals
  suffice; no relational domain is needed until symbolic-size allocation.
- **Architecture: a verifier-resolved index directive.** The stateless
  front-end desugars `x[i]` to a typed-index dialect directive; the verifier
  (the only component that knows every pointer's pointee type, per state)
  resolves it against the run, checks bounds, records the lowering per node
  (which must agree across all explored paths); codegen expands it after
  verification -- constant index to one access, runtime index within one
  homogeneous run to the affine `mul`/`add`/access sequence. This is the
  extraction architecture (F*/Low*, Dafny, SPARK `-gnatp`): the verifier
  checks a model and codegen's fixed expansion is trusted, like the existing
  TLS `la` expansion. A contiguous index interval with uniform element type
  cannot cross a run boundary, so flat `x[i]` needs only {constant, affine,
  refuse}; runtime indexing of *mixed* shapes is refused with a shape-naming
  error (no surveyed language does otherwise), and per-type **offset tables**
  in `.data` are the deferred extension for scattered same-type projections.
  Ranged loads will return the **join** of covered element values (today a
  ranged typed-list `get` is still `ListMultiple`, [§10](#10-known-limitations--todo-map)); ranged stores
  use the flank-preserving weak update (landed in `ranged_weak_update`).
- **Reflection ergonomics**: one-instruction accessor builtins over the
  descriptor record (`typenum`/`typelen`/`subtypes`/`nextrecord`, the Ada
  `'Length` model) replace hand-walked `+16`/`+25` arithmetic; later,
  run-length descriptor records (one record per homogeneous run, the
  DWARF/Go/CLR shape) shrink the blob and make the walk loop-free -- a
  deliberate, separately-measured ABI break.
- **Dynamic memory doctrine: static capacity, runtime length.** Safety
  obligations prove against the capacity (interval-vs-constant, sound today);
  the runtime length lives in a register narrowed by `%`/masks/`require`.
  A symbolic-size `alloc` is the one feature that genuinely needs relational
  facts; deferred.
- **Operators as functions** (direction): a closed operator vocabulary where
  each spelling has a fixed statement-level gathering rule mapping to a
  predefined def header (`d = a + b` gathers as `(dest, lhs, rhs)`; `+=` is
  the `dest == lhs` case of the *same* definition, never a second one);
  scalar cases stay single-instruction primitives; future non-scalar cases
  dispatch through the existing `if typeof` monomorphization. Dereference is
  deliberately **not** an operator: bracketed places already factor `*x = a`
  correctly (the place gathers `x`; the statement side of `=` picks load vs
  store), and `&` stays a builtin.

**Sequencing.** Phase 0 (soundness, landed on this branch): signed-`rem`
interval transfer, flank-preserving weak update for ranged list stores,
`ecall` havocs `a0`. Phase 1a (**landed**): the index directive (`#[` / `#]`)
with the constant index and both refusals, resolved by the verifier and
expanded by codegen. Phase 0.5 (instruction batch, next): `sd` (8-byte stores,
which an element store of a `u64` needs), `andi` plus register `and` (the
one-instruction mask idiom `x[i & 15]`; note 12-bit immediates cap `andi` at
2047), optionally `slli`/`remu`, plus `forget <label>` (region havoc, required
for hosted input through typed buffers). `lbu`/`lhu`/`lwu` are already emitted
for *element* loads (the element's type says how to extend it); adding them to
the **dialect** is what a byte slice would need to close the same gap. Phase
1b: the affine (runtime) index, whose only open question is scratch-register
ownership, and run-length representation inside
`Type`/`MemoryValue`/descriptors. Phase 2:
fork-on-indeterminate (item 3 below), which turns `if i < n:` guards into the
primary narrowing idiom and can make `require` a trap-backed check. Phase 3:
relational facts, widening for beyond-threshold loops, arena `alloc`.
Era-1 honesty: a runtime-indexed load's value can be stored and computed
with, but not branched on, until Phase 2.

**Still open (author decisions):** `require`'s Phase-2 semantics (silent
upgrade vs a new keyword); scratch ownership for indexed stores (user-named
`via` vs a reserved register), the one thing blocking the runtime index.
Settled by Phase 1a: the verified artifact is the **directive model** (codegen's
expansion is trusted, as with the TLS `la`), and the signedness doctrine is
**emit the load that matches the model** wherever the type is known, which is
exactly where element indexing applies; a byte slice keeps the documented
`lb`/`lh` sign-extension mismatch until the dialect has `lbu`/`lhu`.

### Parallelism & SIMD (landed, and the next steps)

**Landed** (see [§6](#6-integration-tests-tests) tests `fannkuch_v2`, `tls_probe`,
`vector_add`, and the **parallel-program obstacles** in [§9](#9-conventions--gotchas)):
- Real multi-hart **work-sharing** (`fannkuch_v2`): block decomposition + per-hart
  thread-local arrays + a lock-free `amoadd`/`amomax` reduction.
- **Per-hart thread-local storage** in codegen (`tp = mhartid * block_size`).
- **`amomax`** (atomic max) and **`fence`** instructions.
- The **register-only RISC-V V subset** (`vsetivli`, `vmv.v.i`, `vadd.vv`,
  `vmv.x.s`), verified and booted (`vector_add`).

**Next steps, in priority order:**

1. **Vectorise the fannkuch flip (the headline SIMD win).** Needs two more vector
   ops the V extension already provides and QEMU already runs (both confirmed):
   - **`vle32.v` / `vse32.v`** (vector load/store). The hard part is the verifier
     model: a vector load reads `vl` consecutive lanes from memory into a
     `MemoryValue::List`. Model it per-lane via the existing scalar
     `find_state_load` / `find_state_store` (loop `i in 0..vl`, offset `i*4`),
     loading each lane into the destination vector register's slot and collecting
     a `List`; mirror for store. Record the accessed range `[rs1, rs1+vl*4)` so
     compaction sees it.
   - **`vrgather.vv`** (gather/permute) -- the SIMD pancake-flip primitive: `vd[i]
     = vs1[vs2[i]]`. Model as indexing the `vs1` lane list by the concrete `vs2`
     index lanes. A reverse-of-first-k flip becomes one `vrgather` with a reversal
     mask, replacing the scalar swap loop.
   Then a `fannkuch_v3`-style SIMD inner loop (permutation in one vector register,
   flips via `vrgather`, find-length via `vmsne`+`vfirst`). This is the ~10-20x
   lever versus the SSE C reference discussed in §7.2.

2. **Weak-memory soundness.** The verifier explores hart interleavings under a
   **sequentially-consistent** model, so multi-hart programs run under round-robin
   TCG (not MTTCG); a `fence` is available but QEMU MTTCG did not reliably honour it
   in testing. Either model weak memory in the verifier or have codegen insert the
   acquire/release fences a verified cross-hart hand-off needs. This connects
   directly to the HPC distributed-verifier plan's determinism guardrails.

3. **Fork on indeterminate comparisons.** `queue_up` errors on an indeterminate
   `bge`/`blt`/`beqz` (e.g. on a `forget`-havoced register) instead of exploring
   both directions. Making it fork would let `forget`/`assume` express any
   data-dependent branch whose direction depends on the runtime `n` (the
   verify-small/run-large branch hazard); `amomax` was the targeted fix for the
   one case (the parallel max-combine) that hit it.

4. **Scale the inner search past 2 harts.** 3-hart verification is infeasible today
   (`queue_up`'s O(N^2) front-search; [§9](#9-conventions--gotchas)). A
   cached/incremental front map removes the O(N^2); beyond that, the
   distributed-verifier rework (this branch, `hpc-distributed-verifier`) is the path
   to verifying larger configurations and hart counts.

### Ambitions

The motivating end-states for the language: a bare-metal OS running DOOM; a
bare-metal Tor node; a bare-metal web server; a bare-metal level-1 hypervisor
as the base of a serverless platform. RISC-V only (aarch64 undecided, x86-64
never). Languages worth stealing from: Lean, Rust, Zig, OCaml, Ada, Mojo,
Python.
