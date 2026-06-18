# formal

A verifying compiler for bare-metal RISC-V. You write a small Python-like
language; the compiler accepts your program only if it can **prove**, by
symbolically executing the machine code across _every_ hardware-thread
interleaving and _every_ admissible type assignment for under-specified
variables, that no assertion can fail and no memory access is ever out of
bounds. The by-products of that proof (the inferred types, and which code is
reachable) then build and shrink the binary.

> **Status: experimental / work in progress.** Much is unimplemented and things
> may break. To work on the compiler, start with
> [DEVELOPMENT.md](DEVELOPMENT.md).

## Requirements

You need only **Rust** (stable) and Cargo (<https://rustup.rs>). Everything else
is handled by the build script.

### Setup is `cargo build` (the single entry point)

The repo's [`build.rs`](build.rs) is the one place that provisions the **system**
dependencies the test suite and the distributed backend need, which Cargo cannot
install itself: a WSL Linux environment on Windows, `qemu-system-riscv64` and a
RISC-V GNU toolchain for the bare-metal boot tests, and a system MPI library for
the (planned) `--features hpc` distributed backend. So:

```sh
cargo build      # builds the compiler AND sets up the environment
```

build.rs detects each dependency and best-effort installs the ones it can do
non-interactively (via the platform package manager); anything that needs admin
or a reboot (installing WSL itself, MS-MPI, a large toolchain) is reported as the
exact command to run. It **never fails the build** (the compiler builds fine with
none of these present; they only enable the QEMU boots / the `hpc` feature) and
is idempotent (it acts only on what is missing). Control it with:

- `FORMAL_NO_SETUP=1` - skip the setup step entirely.
- `FORMAL_SETUP=detect` - report what is missing without installing anything.
- `FORMAL_SETUP=install` - install even under `CI` (the default does not).

The Rust crate dependencies are installed by Cargo as normal.

## Install

```sh
git clone https://github.com/JonathanWoollett-Light/formal
cd formal
cargo install --path .
```

This installs the `formal` command.

## Hello World

`formal new` scaffolds a project, and `cargo run` inside it verifies and
compiles the program end to end:

```sh
formal new hello_world
cd hello_world
cargo run
```

`formal new` writes a starter `main.hl`, so the first `cargo run` just works:

```python
print("Hello World!\n")
exit(0)
```

In the scaffolded project **`cargo run` is the build**: it verifies `main.hl`,
lowers it to RISC-V, then assembles and links it with a RISC-V toolchain it
downloads once into `build/` (through WSL on Windows). The artifacts land in
`build/`:

| File             | What it is                                                    |
| ---------------- | ------------------------------------------------------------- |
| `main.hl`        | the combined source (standard-library prelude + your program) |
| `main.dialect.s` | the annotated RISC-V dialect the compiler verifies            |
| `main.s`         | the verified, runnable RISC-V assembly                        |
| `main`           | the linked RISC-V executable                                  |

Run the executable under QEMU:

```sh
qemu-riscv64 build/main      # -> Hello World!
```

Edit `main.hl`, `cargo run` again, and you have a new binary.

## A taste of the language

Every _simple_ statement maps to one RISC-V instruction, the memory layout is
left implicit (the compiler infers each variable's type and where it lives), and
a `fail` marker is an assertion the compiler must prove can never be reached:

```python
value: global _      # a global variable; let the compiler infer the type
t0 = &value
t1 = 0
t0[0:4] = t1         # value = 0
t1 = t0[0:4]
t1 = t1 + 1          # non-atomic increment (racy across harts)
t0[0:4] = t1
t1 = t0[0:4]
t2 = 4
require t1 < t2      # proven to hold on EVERY interleaving, or the program is rejected
unreachable
```

Control flow is `if` / `while` / `require` blocks (there is no `goto`); the
standard library provides `print` and `exit`; and inline assembly is always one
`asm:` block away. The full language reference, the dialect it compiles to, the
verification model, and how to work on the compiler are in
[DEVELOPMENT.md](DEVELOPMENT.md).

## Documentation

- **[DEVELOPMENT.md](DEVELOPMENT.md)**: the technical reference. The language
  and dialect in full, the compilation/verification pipeline, the test suite,
  and the design notes. Start here to contribute.
- **[comparison.md](comparison.md)**: how `formal` relates to Python, C, C++,
  Rust, Zig, Lean, and Ada/SPARK.
- **[index.html](index.html)**: the project page.
