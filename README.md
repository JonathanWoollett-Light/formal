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
> - The binary entry point ([src/main.rs](src/main.rs)) parses, compresses and
>   prints the AST, then hits `todo!()`; it does not yet run the verifier or emit
>   linkable assembly, so `cargo run` panics — see [Running](#running) below.
> - There is no wiring yet to assemble the output and boot it in QEMU.
>
> For the design intent and a precise description of how compilation works, see
> [CLAUDE.md](CLAUDE.md) and [language.md](language.md).

## The language

`formal` consumes RISC-V assembly extended with comment-prefixed directives that
carry type/verification information. The currently-parsed directives are:

| Directive | Keyword | Meaning |
|-----------|---------|---------|
| `#!` | `fail` | An assertion that must be proven **unreachable**. |
| `#?` | `unreachable` | A point (typically program end) that must be unreachable. |
| `#$ <label> <locality> <type>` | `define` | Declare a variable's locality and/or type. `_` = "infer". |
| `#& <reg>, <label>` | `lat` | Load the address of a label's **runtime type descriptor**. |
| `#@` | `section` | Reserved (designed, not yet implemented). |

`<locality>` is `global`, `thread`, or `_`. `<type>` is a scalar
(`u8`/`i8`/`u16`/`i16`/`u32`/`i32`/`u64`/`i64`), a list `[u8 u8 ...]`, a union
`{u8 i8}`, or `_`. List and union types are never inferred automatically (there
are infinitely many), so they must be given with `#$`.

A minimal example ([assets/four.s](assets/four.s)) — racy increment of a global,
then an assertion that its value stays below 4:

```asm
.global _start
_start:
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
(`three.s` is a complete UART "Hello, World!" with list-type checking).

## Prerequisites

- **Rust** (stable toolchain, edition 2021) and Cargo — https://rustup.rs.
- *(Optional, for the eventual assembly/QEMU workflow)*:
  - The **RISC-V GNU toolchain** (`as`, `ld`, `objcopy`). On Windows the
    simplest route is WSL — see
    https://github.com/riscv-collab/riscv-gnu-toolchain/releases and download
    `riscv64-elf-ubuntu-24.04-gcc`.
  - **QEMU** with `qemu-system-riscv64`. QEMU installs natively on Windows, so
    WSL is not strictly required to *run* the emulator.

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
> programs that do parse (`three`/`four`/`five`/`six`).

### Verifier test suite

```sh
cargo test                 # run all integration tests
cargo test --test three    # run a single test binary
```

The integration tests in [tests/](tests/) drive the full pipeline (parse →
compress → verify → optimize) over the example programs and assert the inferred
types and the optimized output. Exploration is deterministic, so they also pin
the *incremental* behaviour of the verifier state machine: `five`/`six` assert
the exact per-step trace (instruction, hart, configuration and
queue/touched/jumped counts at every step), and `four`/`three` assert the exact
step count and type-inference timeline.

## Assembling and running RISC-V in QEMU

Once `formal` emits linkable assembly (not yet wired up), the intended workflow,
using the RISC-V GNU toolchain (run under WSL on Windows), is:

```sh
# Assemble source to an ELF object file
riscv64-unknown-elf/bin/as -o program.o program.s
# Link the object into an ELF executable
riscv64-unknown-elf/bin/ld -o program.elf program.o
# (Optional) convert the ELF to a raw binary
riscv64-unknown-elf/bin/objcopy -O binary program.elf program.bin
# Boot it under the emulator (you will usually load the ELF)
qemu-system-riscv64 ... program.elf
```

The example programs target the QEMU `virt` machine's UART at physical address
`0x10000000`.

## Further reading

- [CLAUDE.md](CLAUDE.md) — development guidance and a precise, technical
  description of how the compilation/verification process works.
- [language.md](language.md) — design notes: locality/placement, list/union
  exploration, optimization, complexity, and toolchain setup.
