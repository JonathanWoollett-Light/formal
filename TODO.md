# TODOs

Short, medium and long terms things to do.

## Short

- Add example code to index.html which shows how formal implements a borrow
  checker (e.g. smart pointers which assert they have single mutable ownership)
  then show code of it in use side-by-side with equivalent rust code (for the
  side-by-side maybe pull some code that rustlang uses to show why the borrow
  checker matters)
- Adding assertions will always Speedup compilation, thus adding more tests
  actually speeds up code compilation becuase it narrows the validation path,
  add an example to index.html which shows compilation time difference between
  code without assertions and code with it. This should run a test incrementally
  adding assertions, then on the website show a single code block with the
  assertions commented with how much speedup they give.
- Add instructions executed during compilation to the language comparison panels.
- Add more configuration to limit the verification space.
- Add more of the programs from [https://benchmarksgame-team.pages.debian.net/benchmarksgame/index.html] as tests and benchmarks.
- The next uncovered algorithm families are linked lists (Reverse Linked List,
  Merge Two Sorted Lists) and heaps (Top K Frequent Elements). Both need a
  memory region and an allocator first, so they are a second wave after the
  five kernels that landed.
- Standard-library candidates, from an audit of every `tests/*/input.hl` for
  code that is repeated inline and should be shared. `print(0)` was the first
  finding and is fixed; the release fence missing from `parallel_probe` and
  `tls_probe` was the second and is fixed. What is left, most valuable first,
  with the tests each would rewrite. None is urgent: a `def` is inlined, so
  every one of these emits byte-identical code either way, and the win is
  readability, not size.
  - `claim(p)`: the atomic fetch-add-1 rank claim, four hand-written copies
    (`parallel_probe`, `tls_probe`, `fannkuch_v2`, `atomic_claim`). Worth most
    because it hides an `asm:` block, the least checkable construct in the
    language, and the three parallel tests already agree on `a3` as the
    destination.
  - `putc(c)`: write one byte to the QEMU UART, three copies of the bare
    `0x10000000` (`parallel_probe`, `tls_probe`, `uart_hello`). Needs a
    decision first: `std` is Linux-targeted today (`print` and `exit` both
    `ecall`), so this would be its first bare-metal entry.
  - `sum2(p)`: sum two adjacent slots, three byte-identical copies
    (`parallel_probe`, `tls_probe`, `fannkuch_v2`). Narrow, so only worth it
    if the parallel reduction shape stays.
  - `cswap(p)` (adjacent compare-and-swap) and `bucket(x)` (the canonical
    non-negative remainder `((i % d) + d) % d`) each have exactly one call site
    today (`bubble_sort`, `runtime_input`). Deliberately **not** added: one
    call site is not a shared utility. `merge_intervals` looked like a second
    `cswap` site and is not, because it swaps a second array in lockstep on
    the first array's comparison.
  Of the three biggest repetitions in the suite, which are not `def`-shaped at
  all, the array-literal initialiser has landed (`name: thread [u32]*4 =
  [...]`). The other two are still open and designed in DEVELOPMENT.md 11: the
  runtime index `x[i]` (23 occurrences across 14 tests) and an immediate on the
  right of a condition (46 occurrences across 33 tests).
- Roll the array-literal initialiser through the 13 tests that still lay their
  fixtures down a store at a time. The five kernels use it; `bubble_sort`,
  `sieve`, `binary_search`, `signed_bytes`, `dot_product` and the rest do not.
- A list initialiser could emit into `.data` instead of a `la` plus a store per
  element, which would cost **zero** instructions rather than 2n. It needs the
  dialect to carry initial contents, the verifier to seed the variable's memory
  from them, and codegen to emit `.data` for that variable rather than `.bss`.
  Worth doing: `num_islands` spends 40 of its instructions writing a constant
  grid.
- `tests/int_output/input.hl` is a verbatim copy of `std/std.hl`'s integer arm
  that `print_poly` already covers end to end. Reduce it to `print(42)` so its
  `dialect.s` pins the inlined expansion instead.
- `tests/uart_hello/input.hl`'s first 20 lines are a copy of `racy_increment`,
  header comment included, and are unrelated to UART output.
- `fannkuch_v1` and `fannkuch_v2` count their checksum in a unary loop they do
  not need: `if a7 == 0: while t0 != 0: a6 = a6 + 1; t0 = t0 - 1` reduces to
  `if a7 == 0: a6 = a6 + a0`. Strictly better emitted code, and it removes two
  loops from the innermost permutation body.

## Medium

- Add more IO, make a `core` library that has IO agnostic things from `std`.
- Add a test, that tests using AI to re-write Python code into formal code.

## Long

- In the future the verifier will need to be re-written for HPC, it is probably
    best to do this from scratch (I like this philopshy) but should copy good
    features from things like [https://legion.stanford.edu/]
- The compiler should be re-written in the language.