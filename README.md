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

- **Rust** (stable) and Cargo (<https://rustup.rs>) to build the compiler.
- A **RISC-V QEMU** (`qemu-riscv64`) to run the compiled programs.

You do **not** need to install a RISC-V cross-toolchain yourself: a scaffolded
project downloads a pinned one on its first build (and, on Windows, runs it
through WSL).

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
