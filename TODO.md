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
- Standard-library candidates still open, after the audit of every
  `tests/*/input.hl`. Landed: `at`, `at_offset`, `mod`, `fetch_add`,
  `println`, and `print` as two overloads; 19 tests rewritten to use them.
  Deliberately deferred, with the reason each waits:
  - `fill`, `iota`, `copy`, `swap`, `sum2`: fannkuch-only, and `swap`/`sum2`
    would take `a`-registers as std scratch. Two `fill` sites are unsafe
    anyway (fannkuch_v2's loop bound is the value scratch).
  - `at([p, i, size])` with the base already in a register: seven sites, but
    a second clobber set (`t3`) under the same name as the label form.
  - `max([acc, v])`: an in-place first argument needs a way to mark a mutated
    parameter before it reads honestly.
  - `expect([v, k])` (`require` against a literal): about 50 sites, but the
    right fix is `require a3 == 3` in the language, which needs the scratch
    decision DEVELOPMENT.md 11 already tracks; a `t0` scratch is live at a
    dozen of the sites.
  - `uart_digit`: bare-metal and QEMU-specific, two twin probes.
  Left hand-written on purpose, each with a comment: bubble_sort's two index
  computations (the index lives in `t0`, which `at` overwrites), atomic_add
  (pins the raw `amoadd.w`), fannkuch_v2's two `cnt`/`work` fills.
- A translate-time check that a register argument is not also a register
  the body writes (other than a parameter) would have caught all five unsafe
  rewrite sites in the audit, but the natural rule also refuses `exit(a0)`
  and `print(t0)`, which are correct. Needs flow analysis or a narrower rule.
- Zero-arity `def f():` and a call `f()`; today a `def` needs a parameter.
- The other two big repetitions are still open and designed in
  DEVELOPMENT.md 11: the runtime index `x[i]` folded into syntax (`at` is its
  std spelling and owns `t0`/`t1`), and an immediate on the right of a
  condition (46 occurrences across 33 tests).
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