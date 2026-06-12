# formal

A formal-verification compiler for an annotated dialect of RISC-V assembly,
targeting bare-metal RISC-V (e.g. `qemu-system-riscv64`).

Rather than trusting the programmer, `formal` exhaustively explores **every**
hardware-thread (*hart*) interleaving and **every** possible type/locality
assignment for under-specified variables, and proves that no `#!` ("fail")
assertion is reachable on any of them. The by-products of a successful proof are
(a) the inferred type and locality of every variable and (b) the set of
reachable nodes and taken branches, which are then used to dead-code/dead-branch
optimize the program.

> **Status — experimental / work in progress.**
> The parser, the symbolic verifier (`Explorerer`) and the optimizer all exist
> and run. The crate builds as a **library** (`formal`) plus a thin binary. The
> project is **not** yet a turnkey compiler:
> - The verifier is driven through the integration tests in [tests/](tests/),
>   which pass (`cargo test`): they parse, verify and optimize the example
>   programs and assert the inferred types and optimized output.
> - The pipeline can now **emit runnable RISC-V**: from the inferred memory
>   layout it generates the `.data`/`.bss` sections and lowers the verification
>   directives, producing a program the RISC-V GNU toolchain assembles + links
>   into an ELF that boots under `qemu-system-riscv64` (see
>   [Running in QEMU](#running-in-qemu)). The integration tests write these to
>   `target/gen/*.s`, and **dead-data elimination** keeps compile-time-only
>   information (e.g. type-descriptor locality bytes) out of the output.
> - The binary entry point ([src/main.rs](src/main.rs)) parses, compresses and
>   prints the AST, then hits `todo!()`; it does not yet run the verifier or
>   codegen, so `cargo run` panics — that wiring lives in the tests for now (see
>   [Running](#running) below).
>
> For the design intent and a precise description of how compilation works, see
> [CLAUDE.md](CLAUDE.md) and [language.md](language.md).

## The language

`formal` consumes RISC-V assembly extended with comment-prefixed directives that
carry type/verification information. The currently-parsed directives are:

| Directive | Keyword | Meaning |
|-----------|---------|---------|
| `#!` | `fail` | An assertion that must be proven **unreachable**. |
| `#?` | `unreachable` | A point (typically program end) that during compilation if the verifier reaches, it halts, assuming the hart which reached this point turns off (prcatically this may be the hart entering a closed loop at the end of the program). |
| `#$ <label> <locality> <type>` | `define` | Declare a variable's locality and/or type. `_` = "infer". |
| `#& <reg>, <label>` | `lat` | Load the address of a label's **runtime type descriptor**. |
| `#@ <start> <end> <perms>` | `section` | Declare a memory region the program may access (`end` exclusive; perms `r`/`w`/`rw`). Bounds may be immediates or registers — an allocator declares `#@ <base> <base+size> rw` for each allocation it makes. Every raw-address access must fall inside a declared region. |

`<locality>` is `global`, `thread`, or `_`. `<type>` is a scalar
(`u8`/`i8`/`u16`/`i16`/`u32`/`i32`/`u64`/`i64`), a list `[u8 u8 ...]`, a union
`{u8 i8}`, or `_`. List and union types are never inferred automatically (there
are infinitely many), so they must be given with `#$`.

A minimal example ([assets/racy_increment.s](assets/racy_increment.s)) — racy increment of a global,
then an assertion that its value stays below 4. Execution starts from the first
line (like Python — there is no explicit `.global`/`_start:` entry; the runnable
entry point is added by codegen to the program the crate emits):

```asm
    #$ value global _      # `value` is global; let the verifier infer the type
    la t0, value
    li t1, 0
    sw t1, (t0)            # value = 0
    lw t1, (t0)            # non-atomic ...
    addi t1, t1, 1         # ... increment (racy across harts)
    sw t1, (t0)
    lw t1, (t0)
    li t2, 4
    bge t1, t2, _invalid   # require value < 4
    #?                     # must be unreachable
_invalid:
    #!                     # `fail`
```

See [assets/](assets/) for the full set of example programs
(`uart_hello.s` is a complete UART "Hello, World!" with list-type checking).

## Prerequisites

- **Rust** (stable toolchain, edition 2021) and Cargo — https://rustup.rs — to
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

(The build currently emits two harmless `unused import` warnings.)

## Running

### Compiler binary

```sh
cargo run
```

> **Note:** `main` currently hard-codes its input to
> [assets/two.s](assets/two.s) and ends in `todo!()`. `assets/two.s` is written
> with the *readable* `lat`/`branch` spellings, which the parser does not accept
> (it only accepts the canonical `#&` directive and `j`), so `cargo run` panics
> during parsing. Use the test suite below to exercise the verifier against the
> programs that do parse (`uart_hello`/`racy_increment`/`racy_store_inferred`/`racy_store_annotated`).

### Verifier test suite

```sh
cargo test                 # run all integration tests
cargo test --test uart_hello    # run a single test binary
```

The integration tests in [tests/](tests/) drive the full pipeline (parse →
compress → verify → optimize) over the example programs and assert the inferred
types and the optimized output. Exploration is deterministic, so they also pin
the *incremental* behaviour of the verifier state machine: `racy_store_inferred`/`racy_store_annotated` assert
the exact per-step trace (instruction, hart, configuration and
queue/touched/jumped counts at every step), and `racy_increment`/`uart_hello` assert the exact
step count and type-inference timeline.

<a id="running-in-qemu"></a>
## Running in QEMU

The crate lowers each verified + optimized program into a complete, runnable
RISC-V program — the optimized instructions (with the verification directives
lowered) plus the `.data`/`.bss` sections generated from the **inferred** memory
layout. This is the language's core idea: you write assembly with the data layout
*left implicit*, and the verifier figures out the types/locality and writes the
data section for you.

The generated sections also benefit from **dead-data elimination with layout
compaction**: the proof records exactly which bytes the program loads/stores at
runtime — and which instruction computes which offset — so codegen emits only
the accessed bytes and **rewrites the program's address arithmetic in
lockstep**. Information that is only consulted at *compile time* — e.g. each
runtime type descriptor's locality byte, which the example programs never read
— simply does not exist in the output: unaccessed bytes are removed (not
padded), and an instruction whose offset spanned removed bytes has that gap
subtracted from its immediate (`uart_hello`'s descriptor-walking loop strides
`addi t0, t0, 8` instead of the source's 25). Where no single rewritten
immediate can satisfy every execution of an instruction, the region falls back
to `.zero` padding instead — always sound, just less compact.

The integration tests do this end to end: each of `racy_increment`/`racy_store_inferred`/`racy_store_annotated`/`uart_hello`/
`heap_regions` verifies, optimizes, lowers to runnable RISC-V (written to
`target/gen/<name>.s`), pins the exact emitted program (including the absence of
the dead locality data), then **assembles, links, and boots it in QEMU**,
asserting it runs without a CPU fault (`uart_hello` additionally asserts the UART
receives `H`). The RISC-V GNU toolchain and `qemu-system-riscv64` (under WSL)
are **required** — the tests *fail* if they are missing, not skip:

```sh
cargo test                    # verify + lower + boot each program in QEMU
RISCV_BIN=/path/to/riscv/bin cargo test   # point at the toolchain explicitly
```

You can also rebuild + boot the generated files by hand:

```sh
./scripts/build-run.sh        # assemble + link + run target/gen/*.s in QEMU (WSL)
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

`uart_hello` writes `H` to the QEMU `virt` machine's UART (physical address
`0x10000000`) and then halts; `racy_increment`/`racy_store_inferred`/`racy_store_annotated` do racy arithmetic on the
inferred memory and halt in `wfi` (no output). The toolchain is not bundled —
download a prebuilt release (use a stable, not nightly, tag) from
https://github.com/riscv-collab/riscv-gnu-toolchain/releases (e.g.
`riscv64-elf-ubuntu-24.04-gcc.tar.xz`) and run the binaries via WSL.

## Further reading

- [CLAUDE.md](CLAUDE.md) — development guidance and a precise, technical
  description of how the compilation/verification process works.
- [language.md](language.md) — design notes: locality/placement, list/union
  exploration, optimization, complexity, and toolchain setup.
