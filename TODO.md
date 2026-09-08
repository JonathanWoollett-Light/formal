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
- Add leetcode-style algorithm tests, picked to fill the families the suite
  lacks rather than repeat it (`binary_search`, `bubble_sort`, `sieve`, `gcd`
  and `difference_array` already cover binary search, sorting, number theory
  and prefix arrays). Each runs over a small fixed input and ends in a
  `require` on the known answer, so a `Valid` outcome is the proof:
  - Two Sum (hashing). `std` has no hash map, so this is an O(n^2) scan or a
    direct-address table over a bounded value range, with every index into
    that table proven in bounds.
  - Trapping Rain Water (two pointers). Three optimal forms in one problem:
    two pointers, a monotonic stack, and prefix/suffix maxima.
  - Number of Islands (graph traversal). A grid flood fill, so the graph is
    implicit and no allocator is needed; with no recursion the traversal uses
    an explicit worklist.
  - Coin Change (dynamic programming). A 1D table and nested loops.
  - Merge Intervals (sorting and greedy). Reuses `bubble_sort`, then one
    sweep whose correctness rests on an ordering invariant worth proving.
  Linked lists (Reverse Linked List, Merge Two Sorted Lists) and heaps (Top K
  Frequent Elements) are the next uncovered families, but they need a memory
  region and an allocator first, so they belong in a second wave.

## Medium

- Add more IO, make a `core` library that has IO agnostic things from `std`.
- Add a test, that tests using AI to re-write Python code into formal code.

## Long

- In the future the verifier will need to be re-written for HPC, it is probably
    best to do this from scratch (I like this philopshy) but should copy good
    features from things like [https://legion.stanford.edu/]
- The compiler should be re-written in the language.