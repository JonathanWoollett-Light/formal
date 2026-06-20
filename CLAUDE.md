# CLAUDE.md

The technical documentation for this project lives in
**[DEVELOPMENT.md](DEVELOPMENT.md)**: the language and the dialect, the
compilation/verification pipeline, the repository layout, the integration test
suite, conventions/gotchas, and the design notes and roadmap. **Read it before
working on the codebase, and keep it current when behaviour changes** (it is the
canonical, precise description of how everything works).

For usage (installing the CLI, compiling and running a program) see
[README.md](README.md); for positioning against other languages see
[comparison.md](comparison.md).

## Quick reference

- `cargo build`: build the library + `formal` binary; **must stay
  warning-free**.
- `cargo nt` / `cargo nt <name>`: run the test suite (cargo-nextest). The
  QEMU-booting tests require the RISC-V GNU toolchain + QEMU under WSL
  (DEVELOPMENT.md §2).
- `cargo cov` (`--summary-only` / `--html`): run the suite under LLVM code
  coverage via nextest (DEVELOPMENT.md §2). One-time:
  `rustup component add llvm-tools-preview` + `cargo install cargo-llvm-cov`.
- `cargo fmt` / `cargo clippy`: format and lint; `src/verifier.rs` must stay
  clippy-clean (it `#![deny]`s panics/unwraps; DEVELOPMENT.md §9).
- `cargo run -- new <name>`: the `formal` CLI (scaffold a project,
  DEVELOPMENT.md §4.9).
- `cargo run --example translate -- <in.hl> <out.s>`: regenerate a test's
  stored `dialect.s`.

## Working notes

- The tests pin exact incremental behaviour (per-step traces, step counts, type
  timelines) and the exact emitted programs. A behavioural change will
  legitimately break them; **re-derive the expected values from the new
  behaviour, never loosen the assertions to hide a regression** (DEVELOPMENT.md
  §6, §9).
- Keep exploration **deterministic** (order by stable keys, never by pointer
  address): the pinned traces depend on it (DEVELOPMENT.md §4.3).
