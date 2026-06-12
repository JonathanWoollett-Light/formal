#!/usr/bin/env bash
#
# Assemble, link, and run the project's generated RISC-V output in QEMU.
#
# The crate verifies + optimizes each example program and lowers it to a complete,
# runnable RISC-V program (with the `.data`/`.bss` sections the verifier inferred)
# under `target/gen/<name>.s` — written when you run `cargo test` (the
# racy_increment/racy_store_*/uart_hello tests also boot these in QEMU
# themselves). This script rebuilds and boots them by hand with the RISC-V GNU
# toolchain + QEMU.
#
# Prerequisites (run under WSL on Windows):
#   - The RISC-V GNU toolchain (`riscv64-unknown-elf-as` / `-ld`). Point $RISCV at
#     its `bin/` directory, or put the tools on PATH. Prebuilt releases:
#       https://github.com/riscv-collab/riscv-gnu-toolchain/releases
#       e.g. riscv64-elf-ubuntu-24.04-gcc.tar.xz  (use a stable, not nightly, tag)
#   - `qemu-system-riscv64` on PATH (or set $QEMU).
#
# Usage (from the repo root):
#   cargo test                     # verify, lower, and write target/gen/*.s
#   ./scripts/build-run.sh
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
GEN="$ROOT/target/gen"
RISCV="${RISCV:-$HOME/riscv-toolchain/riscv/bin}"
AS="${AS:-$RISCV/riscv64-unknown-elf-as}"
LD="${LD:-$RISCV/riscv64-unknown-elf-ld}"
QEMU="${QEMU:-qemu-system-riscv64}"

if [ ! -d "$GEN" ]; then
    echo "No $GEN — generate it first: cargo test" >&2
    exit 1
fi

for s in "$GEN"/racy_increment.s "$GEN"/racy_store_inferred.s "$GEN"/racy_store_annotated.s "$GEN"/uart_hello.s; do
    name="$(basename "$s" .s)"
    "$AS" -o "$GEN/$name.o" "$s"
    # QEMU `virt` loads `-kernel` at 0x80000000 (RAM) with `-bios none`.
    # `--no-relax`: keep `la` PC-relative — a bare-metal program has no `gp`, so
    # the global-pointer relaxation the linker would otherwise apply produces a
    # bad address.
    "$LD" -Ttext=0x80000000 --no-relax -e _start -o "$GEN/$name.elf" "$GEN/$name.o"
    echo "built $name.elf"
done

echo
echo "Running uart_hello.elf (writes 'H' to the UART at 0x10000000, then halts):"
echo "----"
timeout 3 "$QEMU" -machine virt -bios none -nographic -kernel "$GEN/uart_hello.elf" || true
echo
echo "----"
echo "(racy_increment/racy_store_* do racy arithmetic on the inferred memory and halt in wfi -- no output.)"
