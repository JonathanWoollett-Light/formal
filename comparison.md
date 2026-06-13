# `formal` versus Python, C, C++, Rust, Zig, Lean, and Ada/SPARK

`formal` is a verifying compiler for an annotated dialect of RISC-V assembly,
written through a Python-like surface layer that translates each statement
near one-to-one into the dialect (simple statements one line each; `if`/`while`/
`require` blocks a small fixed pattern each; this document shows the dialect,
since that is what gets verified). Its
defining move is to take a class of correctness properties that other languages
leave to runtime, to testing, to a conservative type rule, or to a human writing
a proof, and to **decide them automatically at compile time** by *symbolically
executing the actual machine code across every hardware-thread (hart)
interleaving and every admissible type/memory layout*.

Concretely, for a program it proves that:

- no `#!` (`fail`) assertion is reachable on **any** interleaving of **any** hart
  ordering, for **any** runtime input;
- **every memory access is verifiable as safe**: in bounds of its (inferred)
  type, or inside a declared raw region (`#@ <start> <end> <perms>`, the
  primitive an allocator uses to hand out memory) with the right permissions;
- it does this while **inferring** the types, locality, and `.data`/`.bss`
  memory layout the program needs (it then emits them), rather than being told;
  and
- the proof's by-products feed code generation: bytes the program was *proven*
  never to touch at runtime are **deleted from the binary**, with the program's
  address arithmetic rewritten in lockstep (dead-data elimination with layout
  compaction).

The cost model is explicit: `O(n · h^r · 2^b · 8^v)` (`n` instructions, `h`
harts, `r` racy instructions, `b` indeterminate branches, `v` unspecified
variables). That single formula is the whole story of where `formal` wins (it
*evaluates the unknown*) and where it loses (the exponents).

This document compares that compile-time evaluation to seven reference points,
with particular weight on the claim that it is a **superset of Zig's `comptime`
and Rust's borrow checker as mechanisms of compile-time reasoning**, and on
deliberately hard comparisons against **Lean** (manual formal proof) and
**Ada/SPARK** (`formal`'s closest industrial peer: automated formal verification
in the wild).

---

## A running example

A global counter `value`, incremented **non-atomically** by every hart, asserted
to stay below 4 (this is essentially
[`tests/racy_increment/`](tests/racy_increment/); in the Python-like surface
the increment reads `t1 = t0[0:4]`, `t1 = t1 + 1`, `t0[0:4] = t1`):

```asm
    #$ value global _      # `value` is global; infer its type
    la t0, value
    li t1, 0
    sw t1, (t0)            # value = 0
    lw t1, (t0)            # read  ─┐ non-atomic
    addi t1, t1, 1         # mod    │ read-modify-write:
    sw t1, (t0)            # write ─┘ racy across harts
    lw t1, (t0)
    li t2, 4
    bge t1, t2, _invalid   # require value < 4
    #?
_invalid:
    #!                     # fail
```

Keep this example in mind. It is a **data race on shared mutable state**, and
`formal` does not forbid the race; it *explores all the interleavings the race
produces* and proves (or refutes) the assertion. Watch how each other language
relates to that.

---

## The one table that frames everything

Compile-time reasoning is a spectrum of *how much the compiler evaluates, and
what it can therefore prove, before the program runs*.

| Language | What it evaluates at compile time | What it proves automatically | Cost / decidability | Verifies |
|---|---|---|---|---|
| **Python** | nothing (just compiles to bytecode) | nothing | trivial | nothing |
| **C** | types | weak type safety; UB everywhere else | linear, decidable | source (then trusts the compiler) |
| **C++** | types + `constexpr`/templates (Turing-complete *concrete* metaprogramming) | type safety + values of *known* expressions | template instantiation, decidable-ish | source |
| **Rust** | types + ownership/borrows/lifetimes | memory safety + data-race-freedom, **conservatively** | ~linear, decidable | source |
| **Zig** | types + `comptime` (*concrete* partial evaluation & metaprogramming) | type safety + asserts on *known* values | ~linear, decidable | source |
| **`formal`** | types (**completely inferred**) + **abstract interpretation over all interleavings, branches, and type assignments** | assertion-unreachability + bounds/permission safety **under races**, for **all inputs**, up to a hart bound | **exponential, bounded** | the **instruction-level program** |
| **Lean** | full dependent types + **manually written proofs** | **any** theorem (functional correctness, …) | undecidable, manual | a model / pure code |
| **Ada/SPARK** | types + **contracts** | absence of run-time errors + your contracts, **deductively** (SMT), for all inputs | modular, decidable-ish, but **prover-incomplete** | source (qualified compiler) |

Two columns do the heavy lifting:

- **"What it evaluates"**: Python evaluates nothing; C/C++/Rust/Zig evaluate
  *types* and (for C++/Zig) *known concrete values*; `formal` evaluates *unknown*
  values (ranges, all type assignments, all interleavings); Lean evaluates a full
  logical model but needs a human to drive it.
- **"Verifies"**: everyone except `formal` verifies a *high-level source* and
  trusts a large optimizing compiler to preserve its semantics down to the
  machine. `formal` verifies at the **instruction level** (real registers,
  real memory, real interleavings), leaving only its own (small, layout-only)
  lowering and the GNU assembler/linker beneath the proof, rather than an
  entire optimizing compiler.

`formal` sits between Zig and Lean: it proves **far more automatically than Zig's
`comptime`** (which proves nothing about runtime-unknown values) yet **far less
than Lean can express**, but it proves it **without a human writing a proof**.

---

## Python

Python is the *no-compile-time-guarantees* baseline. Everything (types, bounds,
attribute existence, concurrency hazards) is discovered, if at all, at runtime.

There is one genuine kinship, recently made literal: a `formal` program, like a
Python script, **starts at the first line** with no `main`/`_start` ceremony.
But that is where it ends. Python *defers* the work `formal` *eliminates*: a
Python program's correctness is established by running it (and its tests) on
particular inputs; a `formal` program's is established by a proof over *all*
inputs and interleavings before it ever runs.

- **`formal` advantage:** every property Python checks at runtime (and most it
  doesn't, like races) is a compile-time theorem; the running example's `value <
  4` is *proved*, not hoped-for.
- **Python advantage:** essentially everything else: expressiveness, libraries,
  productivity, dynamism, and the ability to run programs whose behavior `formal`
  could never afford to enumerate.

---

## C

`formal` and C target the same world: bare metal, manual memory, no runtime, full
control. They are the same *level* and opposite *philosophies*.

C gives you the machine and no safety net: undefined behavior and manual
bounds; its aliasing rules and (since C11) its memory model exist to license
optimization, not to check your program: a data race is simply undefined
behavior, never detected. `formal` operates at that same level
(it *is* assembly) but turns the things C leaves undefined into proof
obligations: out-of-bounds is a verification failure, a write to a read-only or
undescribed memory section is a verification failure, and the running example's
race is exhaustively analyzed rather than silently miscompiled.

- **`formal` advantage:** C's entire catalogue of undefined behavior and silent
  races becomes a compile-time *no*. And because it checks the emitted machine
  code, it sidesteps the "the C compiler was allowed to assume UB couldn't
  happen" class of disasters.
- **C advantage:** maturity, ecosystem, unbounded programs, and a compiler that
  finishes in milliseconds rather than exploring an exponential tree.

---

## C++

C++ is the first reference point with *real* compile-time computation:
`constexpr` and templates form a Turing-complete metaprogramming layer, and
modern C++ can evaluate surprisingly much at compile time.

But that computation is **concrete**: it folds *known* values and instantiates
*known* types. `template<int N>` and `constexpr` reason about compile-time
constants; they do not reason about *the range of values a variable might hold at
runtime*, and they say nothing about thread interleavings. Templates are a *code
generator*; `formal`'s evaluator is a *verifier of runtime behavior*. In the
running example, no amount of `constexpr` can establish `value < 4` under racy
concurrent increments: that fact is about runtime, across threads, which
template evaluation cannot see.

- **`formal` advantage:** proves properties of *runtime-unknown* values and of
  *concurrency*, neither of which C++ compile-time evaluation addresses; plus
  memory-safety and data-race guarantees C++ simply does not have.
- **C++ advantage:** its compile-time layer *generates code* (a different and very
  powerful axis `formal` lacks entirely), and it is a general-purpose language
  with an enormous ecosystem.

---

## Rust: `formal` as the *semantic* superset of the borrow checker

This is one of the two headline comparisons. Rust's borrow checker is a triumph:
a fast, decidable, static analysis that guarantees memory safety and
**data-race-freedom** by enforcing *aliasing XOR mutability*.

The crucial observation is **what kind** of guarantee that is. The borrow checker
proves a **sufficient syntactic condition**: *if* no shared mutable aliasing,
*then* no data races. It is deliberately **conservative**: it rejects programs
that are perfectly safe but violate the discipline. The running example does not
type-check in safe Rust at all: a global mutated by several threads requires a
`Mutex`, an `Atomic`, or `unsafe`. Rust *forbids the race by construction*.

`formal` inverts this. It **admits the racy program** and proves the *actual
semantic property*, "no interleaving of these non-atomic read-modify-writes ever
makes `value` reach 4", by enumerating the interleavings (the `h^r` factor).
This makes it a **superset of the borrow checker as a verifier** in two precise
senses:

1. **It admits strictly more safe programs** (within its bounded,
   finitely-explorable domain). Anything the borrow checker accepts is
   (race-)safe, so its race properties hold trivially under exploration; but
   `formal` *also* accepts and verifies provably-correct racy code: exactly the
   lock-free / intentional-sharing programs for which Rust forces you into
   `unsafe` and *unchecked* reasoning.
2. **It proves a different, often stronger property.** The borrow checker
   proves *race-freedom*; `formal` proves the program's *assertions* hold
   across every interleaving: it does not promise the absence of races, it
   promises the races present are *harmless to everything you asserted*.

Where the relationship reverses (and this matters) is **applicability**:

- The borrow checker is `O(program size)`, decidable, instantaneous, and sound for
  an **unbounded** number of threads (it is a typing rule). `formal` is
  **exponential** in racy instructions and only sound up to a **bounded** hart
  count. So Rust scales to real programs and to "any number of threads" where
  `formal` cannot.
- Rust is a full systems language with an ecosystem; `formal` is annotated
  assembly.

So: `formal` is a superset of the borrow checker in *expressive verification
power* (which programs it can accept, which property it proves), and the borrow
checker is "a superset" in *scalability and unbounded-thread soundness*. The
honest one-liner: **the borrow checker is a fast, conservative approximation of
the race-freedom question; `formal` answers the question itself, exactly, at
exponential cost and bounded thread count.**

**…but you can also opt *into* the borrow checker, and pay its price, not the
exponential.** The whole cost lives in the `h^r` term: interleavings of *racy*
instructions. Avoid unsynchronized shared mutation and `r` collapses, taking the
search with it. `formal` lets you encode that discipline as a **verified library
abstraction** rather than suffer it as a built-in rule: implement an
`std::rc::Rc`-style reference-counted pointer whose borrow invariant is a `#!`
(`fail`) the verifier must prove unreachable, checking the aliasing/ownership
condition at compile time. (The design notes in [CLAUDE.md](CLAUDE.md) anticipate exactly this:
*"borrow checking is, from this verifier's perspective, just a way to
invalidate bad paths faster"*: a reference-counted pointer whose invariant is
a `#!` the proof must show unreachable.) Use such a type throughout
and you have, in effect, **implemented the borrow checker inside `formal`**: only
now the borrow rule is a *checked property of a library*, not a fixed language
feature, and because the program no longer races, its behavior is independent of
hart ordering, so a proof for a small hart count generalizes to any number. You
recover the borrow checker's guarantees **and** its cheap, unbounded-thread cost
profile, while keeping the escape hatch to full interleaving verification for the
provably-correct racy code the borrow checker would reject.

The right mental model, then, is a **dial**, not a fixed point. At one end,
`formal` proves a race *exactly* (maximal precision, exponential cost); at the
other, you adopt a checked ownership abstraction that *forbids* the race, whose
safety is itself proved, recovering borrow-checker economics. The borrow checker
is not something `formal` must be compared *against* from the outside; it is one
setting of `formal`'s own dial.

---

## Zig: `formal` as the *symbolic* superset of `comptime`

The other headline. Zig's `comptime` is the cleanest articulation of
"compile-time evaluation" in a mainstream systems language: arbitrary Zig code
*runs at compile time* for generics, constant folding, and metaprogramming.

But `comptime` is **concrete execution**: it runs the program on *specific, known
values*. It can compute `factorial(5)` or specialize a generic for a known type;
it **cannot** reason about a value whose runtime contents are unknown, and it has
no concept of exploring all execution paths or thread interleavings. Ask
`comptime` whether the running example keeps `value < 4` and it has nothing to
say: the value is a runtime quantity produced by a race.

`formal`'s compile-time evaluation is **symbolic / abstract execution**, and the
superset relationship is exact and rigorous:

> **Concrete execution is the special case of symbolic execution in which every
> value is a singleton.**

`formal` represents each value as an inclusive interval (`MemoryValueU64 { start,
stop }`, a tagged pointer, a list, …). When `start == stop` the value is
*exactly known* (a concrete constant), and operations on exact values produce
exact results: that is constant folding, i.e. *what `comptime` does*. When a
program has no racy unknowns and no unspecified types, `formal`'s exploration
collapses to a **single concrete path**: it literally executes the program at
compile time, exactly like `comptime`. The moment a value becomes unknown (a
race, an input, an unspecified type), `formal` *generalizes* to ranges and
*enumerates* the paths/interleavings/type assignments. `comptime` simply stops
there.

Hence, as a mechanism for reasoning about program behavior, `formal`'s evaluator
**strictly contains** `comptime`'s: it does everything `comptime` does on known
values, and additionally proves universally-quantified properties over *unknown*
values and *all* interleavings.

The caveat, again, is the *other* axis:

- `comptime` is a Turing-complete **metaprogramming and code-generation**
  facility: it *produces* types and functions from compile-time computation.
  `formal` has no metaprogramming layer: its code generation only *lowers* the
  verified program (emitting the inferred layout and compacting it), it never
  synthesizes new program logic. So `comptime` is the superset for
  *metaprogramming*, and `formal` is the superset for *verification of runtime
  behavior*. They generalize concrete compile-time evaluation along different
  axes.
- And `comptime` is cheap and always terminates (on well-formed input); `formal`
  pays the exponential and needs bounded, finitely-explorable execution.

The crisp statement: **`comptime` evaluates the *known* at compile time;
`formal` evaluates the *unknown*, all of it, at compile time.**

---

## Lean: the tough comparison

Lean is the right adversary precisely because it dominates `formal` on the axes
`formal` is weakest on. Lean is a dependently-typed proof assistant: you can
*state and prove arbitrary theorems* (full functional correctness, mathematical
properties, anything expressible in its logic), and the proofs are checked by a
**tiny trusted kernel**, giving extremely high assurance.

Set side by side, the trade is stark and runs in both directions:

| Dimension | Lean | `formal` |
|---|---|---|
| **Expressiveness** | maximal: any theorem in the logic | a **fixed** class: `fail`-unreachability + bounds/permission safety across all interleavings |
| **Automation** | **manual**: you write the proof (tactics, lemmas) | **push-button**: no human proof |
| **What is verified** | a **model** of the program (or pure functional code) | the **RISC-V instructions themselves**, with real memory and real concurrency |
| **Concurrency** | must be **modeled and proved by hand** | **automatic**, by exhaustive interleaving |
| **Completeness** | sound and, in principle, complete for what you can prove | **bounded** (hart count; lists/unions must be written explicitly); *incomplete* beyond the bounds |
| **Trusted base** | a small, audited kernel | a large, `unsafe`, still-maturing symbolic executor |

So Lean is more **expressive**, more **rigorous**, and higher-**assurance**;
`formal` is more **automatic**, operates on the **real executable**, and handles
**concurrency for free**. Lean could certainly prove the running example's `value
< 4`, but you would *manually model* the harts, the non-atomic
read-modify-write, the interleaving semantics, and then *write the proof*.
`formal` discharges the same obligation with a button press, on the literal
assembly, but only up to, say, 4 harts and only for that fixed property shape.

The honest summary is a frontier, not a winner:

- Want an arbitrary correctness theorem about pure logic, with kernel-checked
  assurance, and you have the expertise and patience? **Lean.**
- Want a *fixed* but valuable safety/concurrency property decided *automatically*
  on *real low-level concurrent code*? **`formal`.**

`formal` is best read as **automated, bounded, push-button verification for a
fixed property class on real machine code**: Lean's automation-for-expressiveness
trade, taken to the opposite corner.

---

## Ada/SPARK: the closest peer

If Lean is the hardest comparison on *expressiveness*, **SPARK** is the hardest on
*everything practical*. SPARK is a formally analyzable subset of Ada plus a prover
(GNATprove) that does **automated formal verification** of real systems code: it
proves **absence of run-time errors** (no overflow, no out-of-bounds, no division
by zero, no null dereference) and discharges user-written **contracts**
(pre/post-conditions, type invariants, loop invariants) with SMT solvers. It is
**industrial**: qualified for DO-178C / EN 50128 / Common Criteria, shipping in
aerospace, rail, and security products for decades. It occupies almost exactly
`formal`'s stated niche (*automatic, sound, compile-time verification of
safety-critical low-level code*), which makes the differences the most
instructive in this document.

They verify by **opposite techniques**, and almost every trade-off follows from
that:

- **Deductive & modular (SPARK)** vs **operational & whole-program (`formal`).**
  SPARK reasons with Hoare logic / weakest-preconditions, function-by-function
  against contracts, and hands verification conditions to an SMT solver. This
  **scales** (it verifies large programs modularly and is sound for unbounded
  data and threads), but it needs you to **write the contracts** (and often the
  *loop invariants* and occasional helper lemmas), and the SMT backend is
  **incomplete**: a true verification condition can fail to be discharged
  ("prover times out"), and you must add assertions to guide it. `formal` instead
  *symbolically executes the whole program's state space*: it needs **no
  contracts and no loop invariants** for its properties, is **exact** (and, for
  type inference, **complete**) over the space it explores, but is
  **non-modular**, **exponential**, and **bounded** (hart count; explicit
  lists/unions only).

- **Concurrency: restrict-and-prove vs explore-and-verify.** SPARK proves
  data-race- and deadlock-freedom only within a **restricted tasking model**
  (the Ravenscar/Jorvik profiles: no dynamic tasks, shared state behind protected
  objects, ceiling-priority locking). Like Rust's borrow checker, it *forbids the
  dangerous patterns* and proves the disciplined remainder safe by flow analysis;
  it does **not** exhaustively analyze arbitrary interleavings of genuinely racy,
  unsynchronized code. `formal` does exactly that (the `h^r` exploration), so it
  can **verify intentionally-racy lock-free code that SPARK's model rejects**.
  That is the same superset relationship as with the borrow checker, and the same dial:
  `formal` *can* adopt a restrict-and-prove discipline to recover SPARK/Ravenscar
  economics, but its default is to explore.

- **Source vs instruction level.** SPARK verifies **Ada source** and relies on
  a (qualified) compiler beneath it; `formal` verifies the **instruction-level
  program**, shrinking that trust gap to its own layout lowering plus the
  assembler/linker, at the cost of working only on annotated assembly with
  none of Ada's expressiveness, libraries, or tooling.

- **Explicit types vs inferred types.** SPARK leans on Ada's rich *explicit*
  type/subtype/range declarations: you *state* `Index range 1 .. N`, and the
  prover uses it. `formal` *infers* the types and memory layout (the complete
  `8^v` search) and emits them. SPARK asks you to specify the representation
  precisely; `formal` discovers it.

Netted out:

- **SPARK advantages:** mature, qualified, productized; modular and therefore
  *scalable*; sound for unbounded data and threads; and *expressive*: arbitrary
  functional contracts, not a fixed property shape. It is the existence proof that
  this entire niche is viable and shippable, and `formal` is, by every practical
  measure, decades behind it.
- **`formal` advantages:** no contracts or loop invariants for its property class
  (more automatic than SPARK's gold/platinum levels, which need proof guidance);
  exhaustive over *arbitrary* racy interleavings rather than a restricted tasking
  model; verifies the machine code directly; and infers types/locality/layout
  rather than requiring them. Where SPARK *restricts concurrency to prove it
  cheaply*, `formal` *explores concurrency to verify it exactly*.

The fair summary: **SPARK and `formal` are the two closest entries here.** SPARK
is the deductive, modular, contract-driven, *industrial* point in the design
space; `formal` is the operational, whole-program, contract-free, *exhaustive*
point, trading SPARK's scale, maturity, and expressiveness for zero annotation
burden, machine-code-level assurance, complete inference, and exact verification
of the racy code SPARK would forbid.

---

## Where `formal` is genuinely novel

Stepping back, four capabilities are unusual *in combination*, and none of the
others offer all four automatically:

1. **It verifies at the instruction level, not the source level.** Every other
   entry verifies a high-level artifact and trusts an optimizing compiler
   beneath it. `formal`'s proof is about the instructions themselves; what
   remains beneath it is only its own layout-emitting lowering (which rewrites
   immediates but never re-orders or re-selects instructions) and the
   assembler/linker: a far smaller trust gap, though not zero.
2. **It proves properties across all thread interleavings, automatically.** Rust
   *forbids* races, Lean makes you *model* them; `formal` *explores* them.
3. **Its type inference is *complete*, not merely convenient** (the `8^v`
   dimension). Conventional inference (Hindley–Milner, Rust, Zig) *unifies local
   constraints*: it is fast but **incomplete**, so it can fail to infer, demand an
   annotation, or reject an under-specified-but-valid program, and the type it
   picks is only checked locally. `formal` instead *searches the type space and
   verifies each candidate against the whole program*: a variable left `_` is
   tried as every scalar type × locality, and a typing is accepted **iff it makes
   the entire program verify**. Inference is therefore **essentially infallible**:
   if *any* typing makes the program correct, it is found, and the inferred type
   is by construction one under which the program *provably* works (there is no
   second-stage "the inferred type doesn't satisfy the checker" failure, because
   inference and verification are the *same* search). It then *emits* the
   `.data`/`.bss` that typing implies: the program describes *behavior*, and the
   verifier discovers the *representation* that makes it correct. Two honest
   asterisks on "infallible": lists and unions are infinite, so they must be given
   explicitly with `#$` rather than inferred; and the guarantee is **complete but
   not cheap**: `8^v` (times `h^r`) means the search, while it never *fails* to
   find an existing typing, can quickly become **intractable** as the number of
   unspecified variables, harts, or races grows.
4. **The proof optimizes the binary: dead *data* elimination, not just dead
   code.** Every compiler deletes unreachable code; `formal`'s proof also knows
   exactly which *bytes of memory* the program can touch at runtime, across all
   interleavings, so codegen emits only those bytes and **rewrites the address
   arithmetic to match**: in the Hello-World example, runtime type descriptors
   shrink from 25-byte records to just their read fields, and the loop that
   strides them is rewritten from `addi t0, t0, 25` to `addi t0, t0, 8`.
   Information consumed only by the verifier (e.g. each descriptor's locality
   byte) does not exist in the output at all. Linkers garbage-collect whole
   unreferenced sections; profile-guided optimizers act on *observed* runs.
   Nothing else deletes interior bytes of *live* data because a proof showed
   every runtime path misses them.

---

## Where `formal` loses, honestly

The same design that gives the strengths above caps them hard:

- **Combinatorial blow-up.** `O(n · h^r · 2^b · 8^v)`. Many racy instructions,
  several harts, many indeterminate branches, or many unspecified variables (the
  `8^v` type search), and the exploration is simply infeasible. Type inference
  never *fails*, but it can run out of time or memory. Real concurrent programs
  live exactly where the exponents bite; the hart count is the one bound you
  choose today (list/union exploration knobs are designed but unimplemented;
  lists and unions must currently be written explicitly).
- **Bounded ⇒ incomplete.** Soundness is only up to the chosen hart counts. A
  proof for ≤4 harts is *not* a proof for all harts, unlike Rust's
  race-freedom or a Lean theorem, which are unbounded.
- **A narrow, fixed property class.** It proves `fail`-unreachability and memory
  safety; it does not (and cannot, as built) express arbitrary functional
  correctness the way Lean can.
- **Finitely-explorable execution only.** Programs need statically-bounded loops;
  unbounded or input-shaped iteration breaks the finite execution tree.
- **Low-level ergonomics.** The Python-like surface layer is still
  assembly-shaped: explicit registers and byte-slice loads/stores, with `if`/
  `while`/`require` the only control flow. There are no expressions, no
  functions, no ecosystem, no libraries.
- **Maturity and trusted base.** The verifier is a large body of `unsafe`
  pointer code under active development: its soundness rests on *its own*
  correctness (a far larger trusted base than Lean's kernel or Rust's type
  system), and it is partial (unhandled constructs surface as `Unsupported`
  errors rather than proofs).

---

## Bottom line

| | Python | C | C++ | Rust | Zig | **`formal`** | Lean | Ada/SPARK |
|---|---|---|---|---|---|---|---|---|
| Compile-time eval of *unknown* values | no | no | no | partial (types) | no | **yes** | yes (manual) | yes (deductive) |
| Proves assertions hold under races | no | no | no | n/a (forbids races) | no | **yes (exhaustive)** | yes (manual) | n/a (restricts races) |
| Admits provably-correct racy code | n/a | yes (unchecked) | yes (unchecked) | only via `unsafe` | yes (unchecked) | **yes (checked)** | yes (manual) | no (restricts) |
| Verifies at the instruction level | no | no | no | no | no | **yes** | no | no |
| Type inference | n/a | no | no | local (incomplete) | local (incomplete) | **complete (bounded)** | no | no |
| Infers memory layout | no | no | no | no | no | **yes** | no | no |
| Proof-driven dead-*data* elimination | no | no | no | no | no | **yes** | no | no |
| Automatic (no manual proof) | n/a | yes | yes | yes | yes | **yes** | **no** | mostly (contracts) |
| Arbitrary functional correctness | no | no | no | no | no | no | **yes** | yes (contracts) |
| Unbounded threads / scale | n/a | n/a | n/a | **yes** | n/a | **no** | yes | yes |
| Cheap / fast | yes | yes | mostly | yes | mostly | **no** | no | mostly |

`formal`'s thesis, in one sentence: **it generalizes compile-time evaluation from
Zig's concrete partial evaluation to full symbolic exploration, and turns Rust's
conservative race *prohibition* into a *dial*: from exact race *verification* at
one end to the borrow checker's cheap prohibition (recovered as a verified `Rc`
abstraction) at the other, paying, at the precise end, with an exponential
bounded search over real machine code, and stopping well short of Lean's
expressive, kernel-checked, but human-driven proofs.**
