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

## Medium

- Add more IO, make a `core` library that has IO agnostic things from `std`.
- Add a test, that tests using AI to re-write Python code into formal code.

## Long

- In the future the verifier will need to be re-written for HPC, it is probably
    best to do this from scratch (I like this philopshy) but should copy good
    features from things like [https://legion.stanford.edu/]
- The compiler should be re-written in the language.