# formal

A formal-verification compiler targeting bare-metal RISC-V (e.g.
`qemu-system-riscv64`). Programs are written in a Python-like language (not
yet named; working name `hl`) that translates **one statement to one line** of
an annotated RISC-V assembly dialect; the dialect is what gets verified and
compiled.

Rather than trusting the programmer, `formal` exhaustively explores **every**
hardware-thread (*hart*) interleaving and **every** possible type/locality
assignment for under-specified variables, and proves that no `#!` ("fail")
assertion is reachable on any of them. The by-products of a successful proof are
(a) the inferred type and locality of every variable and (b) the set of
reachable nodes and taken branches, which are then used to dead-code/dead-branch
optimize the program.

> **Status: experimental / work in progress.**
> The parser, the symbolic verifier (`Explorerer`) and the optimizer all exist
> and run. The crate builds as a **library** (`formal`) plus a thin binary. The
> project is **not** yet a turnkey compiler:
> - The verifier is driven through the integration tests in [tests/](tests/),
>   which pass (`cargo nt`): they translate each test's `.hl` source (pinning
>   the exact stored dialect), parse, verify and optimize it, assert the
>   inferred types and the exact emitted output, and boot the results in QEMU
>   (`uart_hello` prints `Hello World!` over the UART).
> - The pipeline can now **emit runnable RISC-V**: from the inferred memory
>   layout it generates the `.data`/`.bss` sections and lowers the verification
>   directives, producing a program the RISC-V GNU toolchain assembles + links
>   into an ELF that boots under `qemu-system-riscv64` (see
>   [Running in QEMU](#running-in-qemu)). The integration tests write these to
>   `target/gen/*.s`, and **dead-data elimination** keeps compile-time-only
>   information (e.g. type-descriptor locality bytes) out of the output.
> - The binary ([src/main.rs](src/main.rs)) is the **`formal` CLI**:
>   `formal new <name>` scaffolds a project whose `cargo run` verifies and
>   compiles its `main.hl` end to end into `build/` (the whole pipeline is also
>   the one library call `formal::compile`). See [Compiler binary](#compiler-binary).
>
> For a precise description of how compilation works (and the design intent
> behind it), see [CLAUDE.md](CLAUDE.md); for how `formal` relates to other
> languages, see [comparison.md](comparison.md).

## The language

Two layers, kept deliberately close:

1. **The Python-like surface** (working name `hl`) is what you write. Every
   simple statement lowers to exactly one line of the dialect below, and the
   structured statements (`if`/`while`/`require`) each lower to a fixed pattern
   of a branch or two plus generated labels: no register allocation, no
   implicit control flow beyond those patterns, no code synthesis. Like C's
   near one-to-one mapping onto assembly, the cost of every line is visible at
   the call site, and inline assembly is always available through the `asm:`
   block (spelled like `if:`).
2. **The annotated RISC-V dialect** is the verification target: RISC-V assembly
   extended with comment-prefixed directives that carry type/verification
   information.

Control flow is **structured only**: there is no `goto` and there are no labels
in the surface language. The simple statement forms and their dialect
translations:

```text
value: global _              ->  #$ value global _        variable definition (locality/type; _ = infer)
welcome: _ [u8]*13           ->  #$ welcome _ [u8 ... u8]  list types: [u8, u8] or [u8]*n
t0 = &value                  ->  la t0, value              address of a variable
t0 = type(welcome)           ->  #& t0, welcome            address of the runtime type descriptor
t0 = csr(mhartid)            ->  csrr t0, mhartid          read a CSR (which hart am I?)
t1 = 0x10000000              ->  li t1, 0x10000000         load immediate (radix preserved)
t1 = t1 + 1                  ->  addi t1, t1, 1            register +/- immediate
t0[0:4] = t1                 ->  sw t1, 0(t0)              store: byte slice (width 1 = sb, 4 = sw)
t1 = t0[8:16]                ->  ld t1, 8(t0)              load: byte slice (1 = lb, 4 = lw, 8 = ld)
section 0x100 0x200 rw       ->  #@ 0x100 0x200 rw         declare an accessible memory region
fail                         ->  #!                        assertion: must be proven unreachable
unreachable                  ->  #?                        end of execution (hart halts)
asm:                         ->  (each indented line       inline assembly, verbatim
    wfi                           emitted verbatim)
```

The structured statements take a condition `<reg> <op> <reg>` (with
`<`/`<=`/`>`/`>=`/`==`/`!=`, or `<reg> ==|!= 0`) and an indented block:

```text
require t1 < t2              # fail unless t1 < t2 (one line: `if not <cond>: fail`)

if t0 == 0:                  # run the block when the condition holds
    t1 = t0[0:8]

while t5 != t2:              # top-tested loop
    t5 = t5 + 1
```

`#` starts a comment, exactly as in Python. Loads and stores are byte slices
off a register (`reg[offset : offset+len]`), so the access width is explicit.

**Functions and a standard library.** `def name(param):` + an indented block
declares an **inline** function; a call `name(arg)` is expanded in place (no
calling convention, stack, or `ret`), with the argument a `"string"` literal or
an integer. The compiler prepends a single standard-library file
([std/std.hl](std/std.hl), itself written in this dialect) to every program; a
`def` emits no code until called, so the prelude is free for programs that do
not use it. The library functions today are `print` (write a string to stdout,
Linux syscall 64) and `exit` (end the process, syscall 93); both use `ecall`,
so they target a hosted (Linux) process. The `linux_hello` test compiles a
two-line `print("Hello World!\n")` + `exit(0)` to a static RISC-V ELF and runs
it under `qemu-riscv64`; the bare-metal `uart_hello` cannot use them (no OS to
answer the `ecall`) and pokes the QEMU UART with raw assembly instead.

The dialect's directives, which the verifier consumes:

| Directive | `hl` form | Meaning |
|-----------|-----------|---------|
| `#!` | `fail` | An assertion that must be proven **unreachable**. |
| `#?` | `unreachable` | End of execution: a hart that reaches this point halts (practically, this is the hart parking in a closed `wfi` loop at the end of the program). |
| `#$ <label> <locality> <type>` | `name: <locality> <type>` | Declare a variable's locality and/or type. `_` = "infer". |
| `#& <reg>, <label>` | `reg = type(name)` | Load the address of a label's **runtime type descriptor**. |
| `#@ <start> <end> <perms>` | `section <start> <end> <perms>` | Declare a memory region the program may access (`end` exclusive; perms `r`/`w`/`rw`). Bounds may be immediates or registers: an allocator declares each allocation as it makes it. Every raw-address access must fall inside a declared region. |

`<locality>` is `global`, `thread`, or `_`. `<type>` is a scalar
(`u8`/`i8`/`u16`/`i16`/`u32`/`i32`/`u64`/`i64`), a list, a union `{u8 i8}`, or
`_`. List and union types are never inferred automatically (there are
infinitely many), so they must be written explicitly (`welcome: _ [u8]*13`).

A minimal example ([tests/racy_increment/input.hl](tests/racy_increment/input.hl)): racy increment of a
global, then an assertion that its value stays below 4. Execution starts from
the first line (like Python: there is no explicit `.global`/`_start:` entry;
the runnable entry point is added by codegen to the program the crate emits):

```python
value: global _      # `value` is global; let the verifier infer the type
t0 = &value

t1 = 0               # value = 0
t0[0:4] = t1

t1 = t0[0:4]         # non-atomic ...
t1 = t1 + 1          # ... increment (racy across harts)
t0[0:4] = t1

t1 = t0[0:4]
t2 = 4
require t1 < t2      # must hold on every interleaving
unreachable
```

which translates near-1:1 to the dialect ([tests/racy_increment/dialect.s](tests/racy_increment/dialect.s))
(`require` becomes a branch over the `#!` fail marker, with a generated label):

```asm
    #$ value global _
    la t0, value
    li t1, 0
    sw t1, 0(t0)
    lw t1, 0(t0)
    addi t1, t1, 1
    sw t1, 0(t0)
    lw t1, 0(t0)
    li t2, 4
    blt t1, t2, _l0
    #!
_l0:
    #?
```

See the [tests/](tests/) folders for the full set of example programs (each
holds a program's `.hl` source next to its stored dialect translation);
[tests/uart_hello/input.hl](tests/uart_hello/input.hl) is a complete UART
`Hello World!` with runtime list-type checking: the program inspects its own
inferred type descriptors before printing.

## Prerequisites

- **Rust** (stable toolchain, edition 2021) and Cargo (https://rustup.rs) to
  build the crate.
- **Required to run the test suite** (the integration tests assemble + boot each
  program's output, and *fail* if these are missing):
  - The **RISC-V GNU toolchain** (`riscv64-unknown-elf-as`/`-ld`), run under WSL.
    Download a stable release from
    https://github.com/riscv-collab/riscv-gnu-toolchain/releases (e.g.
    `riscv64-elf-ubuntu-24.04-gcc`) and extract it into WSL; point `RISCV_BIN` at
    its `bin/` (default `$HOME/riscv-toolchain/riscv/bin`).
  - **QEMU** with `qemu-system-riscv64` on the WSL PATH.

## Building

```sh
cargo build
```

## Running

### Compiler binary

The `formal` binary is a small CLI. Install it (`cargo install --path .`), then
scaffold a project:

```sh
formal new hello_world
cd hello_world
cargo run                # verify + compile main.hl into build/
```

`formal new <name>` runs `cargo new`, adds `formal` as a (GitHub) dependency,
and writes a starter `main.hl` ("Hello World!" in the Python dialect, using the
`print`/`exit` standard library) plus a build-script `src/main.rs`. In the new
project, **`cargo run` is the build**: it calls `formal::compile`, writing into
`build/`

- `main.hl`: the combined source (standard-library prelude + your program),
- `main.dialect.s`: the annotated RISC-V dialect,
- `main.s`: the verified, runnable RISC-V assembly,
- `main`: the linked executable.

The toolchain stages assemble + link with the RISC-V GNU toolchain, which
`cargo run` **downloads once into `build/toolchain`** (and runs through WSL when
present, so it works on Windows). The whole pipeline is also exposed as the one
library call `formal::compile(source) -> Result<Compiled, _>`.

### Translator

```sh
cargo run --example translate -- program.hl program.s   # hl -> dialect, to a file
cargo run --example translate -- program.hl             # ... or to stdout
```

The translation is line-for-line, so a translation error reports the offending
source line (`line 12: unsupported store width 2 (1 or 4)`). This is also how
the stored `dialect.s` beside each test's `input.hl` is regenerated when a
program changes.

### Verifier test suite

```sh
cargo nt              # run all tests (nextest: one clean line per test)
cargo nt uart_hello   # run a specific test
cargo test            # works too (noisier per-binary output)
```

[cargo-nextest](https://nexte.st) is the recommended runner: install once with
`cargo install cargo-nextest` (or grab a prebuilt from https://get.nexte.st).
It prints one green/red line per test and runs the test binaries in parallel,
so the whole suite (including the QEMU boots) finishes in roughly the time of
the slowest test. The console carries only this concise per-test data; the
**live progress** of long tests streams to files instead:

```powershell
Get-Content -Wait target/tmp/uart_hello.verify.progress   # verifier step count
Get-Content -Wait target/tmp/uart_hello.qemu.progress     # QEMU elapsed + executed instructions
```

> **Note:** the QEMU tests spawn `wsl.exe`, which, if it attaches to the
> parent console, mutates the console mode and corrupts all subsequent output
> in that window (the "staircase" effect; in-place progress bars print a new
> line per redraw). The test helper therefore spawns WSL detached from the
> console (`CREATE_NO_WINDOW`), so any runner's output renders correctly.
> `cargo nt` is a repo alias for `nextest run`
> ([.cargo/config.toml](.cargo/config.toml)); if your console still
> mis-renders live progress, add `--show-progress none`.

The integration tests in [tests/](tests/) drive the full pipeline (translate →
parse → compress → verify → optimize) over the example programs. Each test
lives in its own folder with its assets: the `.hl` source, the stored dialect
(pinned as the translator's exact output), and the expected optimized/emitted
stages. Exploration is deterministic, so the tests also pin the *incremental*
behaviour of the verifier state machine: `racy_store_inferred`/`racy_store_annotated` assert
the exact per-step trace (instruction, hart, configuration and
queue/touched/jumped counts at every step), and `racy_increment`/`uart_hello` assert the exact
step count and type-inference timeline.

<a id="running-in-qemu"></a>
## Running in QEMU

The crate lowers each verified + optimized program into a complete, runnable
RISC-V program: the optimized instructions (with the verification directives
lowered) plus the `.data`/`.bss` sections generated from the **inferred** memory
layout. This is the language's core idea: you write assembly with the data layout
*left implicit*, and the verifier figures out the types/locality and writes the
data section for you.

The generated sections also benefit from **dead-data elimination with layout
compaction**: the proof records exactly which bytes the program loads/stores at
runtime (and which instruction computes which offset), so codegen emits only
the accessed bytes and **rewrites the program's address arithmetic in
lockstep**. Information that is only consulted at *compile time* (e.g. each
runtime type descriptor's locality byte, which the example programs never read)
simply does not exist in the output: unaccessed bytes are removed (not
padded), and an instruction whose offset spanned removed bytes has that gap
subtracted from its immediate (`uart_hello`'s descriptor-walking loop strides
`addi t0, t0, 8` instead of the source's 25). Where no single rewritten
immediate can satisfy every execution of an instruction, the region falls back
to `.zero` padding instead: always sound, just less compact.

The integration tests do this end to end: each of `racy_increment`/`racy_store_inferred`/`racy_store_annotated`/`uart_hello`/
`heap_regions` verifies, optimizes, lowers to runnable RISC-V (written to
`target/gen/<name>.s`), pins the exact emitted program (including the absence of
the dead locality data), then **assembles, links, and boots it in QEMU**,
asserting it runs without a CPU fault (`uart_hello` additionally asserts the
UART receives the full `Hello World!`). The RISC-V GNU toolchain and `qemu-system-riscv64` (under WSL)
are **required**; the tests *fail* if they are missing, not skip:

```sh
cargo nt                    # verify + lower + boot each program in QEMU
RISCV_BIN=/path/to/riscv/bin cargo nt   # point at the toolchain explicitly
```

You can also rebuild + boot the core examples by hand (the script hard-codes
the four `racy_*`/`uart_hello` programs):

```sh
./scripts/build-run.sh        # assemble + link + boot them in QEMU (WSL)
```

[scripts/build-run.sh](scripts/build-run.sh) drives the RISC-V GNU toolchain and
QEMU; point `$RISCV` at the toolchain `bin/` directory (or put the tools on
PATH). The essential steps it (and the tests) run per program are:

```sh
riscv64-unknown-elf-as -o program.o program.s
# `--no-relax`: keep `la` PC-relative; a bare-metal program has no `gp` for the
# global-pointer relaxation the linker would otherwise apply.
riscv64-unknown-elf-ld -Ttext=0x80000000 --no-relax -e _start -o program.elf program.o
qemu-system-riscv64 -machine virt -bios none -nographic -kernel program.elf
```

`uart_hello` writes `Hello World!` to the QEMU `virt` machine's UART (physical
address `0x10000000`) and then halts; `racy_increment` does a racy increment
and `racy_store_inferred`/`racy_store_annotated` racy stores on the inferred
memory, all halting in `wfi` (no output). The toolchain is not bundled:
download a prebuilt release (use a stable, not nightly, tag) from
https://github.com/riscv-collab/riscv-gnu-toolchain/releases (e.g.
`riscv64-elf-ubuntu-24.04-gcc.tar.xz`) and run the binaries via WSL.

## Further reading

- [CLAUDE.md](CLAUDE.md): development guidance, a precise, technical
  description of how the compilation/verification process works, plus the
  design notes and roadmap.
- [comparison.md](comparison.md): how `formal`'s compile-time evaluation
  relates to Python, C, C++, Rust, Zig, Lean, and Ada/SPARK.
- [index.html](index.html): the marketing page.
