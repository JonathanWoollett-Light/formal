# CLAUDE.md

Generic rules and best practices: everything in this file should apply to
broadly any project of this kind (a Rust systems project), not just this one.
Project-specific content lives elsewhere, and the separation is deliberate:

- **[DEVELOPMENT.md](DEVELOPMENT.md)**: the project-specific knowledge and
  decisions. The language and the dialect, the compilation/verification
  pipeline, the repository layout, the integration test suite,
  conventions/gotchas, and the design notes and roadmap. **Read it before
  working on the codebase, and keep it current when behaviour changes** (it is
  the canonical, precise description of how everything works). §2 lists every
  command: `cargo build` (must stay warning-free), `cargo nt`, `cargo cov`,
  `cargo fmt` / `cargo clippy`, the `translate` example, and the `BLESS=1`
  comparisons pipeline (§6.1).
- **[README.md](README.md)**: the project-specific instructions. Setup
  (`cargo build` is the single entry point), installing the CLI, compiling and
  running a program. Configuration intended to be read by humans belongs here.
- **[comparison.md](comparison.md)**: positioning against other languages.

Integrate decisions made in chat into the right document as they are made:
generic rules here, project knowledge and decisions in DEVELOPMENT.md,
project instructions in README.md. When updating the code or any of these
documents, update the others to match and remain consistent.

## Workflow

- Commit after each prompt that made a change, so no prompt leaves the
  repository with uncommitted changes (and never edit uncommitted changes in
  a new prompt). Where the changes belong with an existing commit that has
  not been pushed yet, amend that commit instead of creating a new one.
- When outputting console commands, output them so they can be executed at the
  project root.
- Always output the command-line commands to test changes. If continuing
  requires a compute-intensive run, output the command piping to a temp file,
  let the user execute it, and continue the chat after it has run.
- Always add timeouts to all background tasks, and actively report their
  progress by piping their output to a temp file the user can read. Never
  start high-utilisation background tasks (anything that would saturate the
  machine, e.g. a full verification run or the QEMU comparison measurements):
  hand the command to the user instead.
- Leave handoff context after each prompt so a new chat can pick up where the
  last one left off, even for work that was only planned: integrate it into
  the documents above (here, DEVELOPMENT.md's design notes and roadmap)
  rather than leaving it only in chat.

## Code

- The best code is no code: always push towards simpler, smaller code using
  existing tooling and libraries. Prefer a well-maintained, popular crate over
  hand-rolling (e.g. indicatif for progress bars). The minimal-footprint
  preference is about *direct* dependencies (the ones listed in `Cargo.toml`):
  keep those few and well-justified; transitive dependencies are a much lesser
  concern and should not be a significant factor in a trade-off.
- Optional features should add no *required* dependency: lean on the standard
  library and universal tools already present, so a user who never touches the
  feature pays nothing for it. Any feature that provisions a paid/external
  resource must tear it down in a `finally`-equivalent path, so an error or
  interrupt never leaks it.
- There should be no prerequisite setup beyond the ecosystem's standard entry
  point: a missing dependency is detected and installed when the user runs
  what needs it (here `build.rs` under `cargo build`; see the README "Setup"
  section).
- Prefer repo-side mechanisms (cargo aliases, `build.rs`, checked-in config)
  over per-machine configuration files.
- Anything that could realistically run longer than a second gets progress
  tracking: a progress bar or spinner (hierarchical where there are subtasks,
  overall progress above current task) with system utilisation reported
  alongside, or log lines where a live display would corrupt output (here the
  tests stream tail-able reports into `target/tmp/test-logs/`). The console
  shows progress; historical detail (e.g. per-task timings after each task)
  goes to a log file.
- Avoid Object-Oriented-Programming-style design: trait/interface indirection,
  dependency injection, and type hierarchies introduced for their own sake or
  for testability. Prefer plain functions over concrete data; introduce an
  abstraction only once a second real implementation exists.
- Comments are either short and inline (`let x = 2; // short comment`) or full
  lines preceding the code; never multi-line inline comments.
- Prefer TOML to YAML.

## Testing and measurement

- **One real end-to-end approach; no shims or mocks.** There is one canonical
  way to test: run the real entry points unmodified (here `cargo build`, which
  is also setup, then the test suite), and move that same sequence wherever
  coverage is needed, e.g. executing it inside an empty factory-default VM to
  test setup itself. Never fake the environment (stubbed `wsl`/`sudo`/PATH
  binaries, mocked commands) and never restructure code to create mockable
  seams: shims and mock-heavy unit testing add confounds and complexity that
  make a project worse. The only test-specific flag such a run may need is a
  recursion guard, so the suite running inside a VM does not spawn another VM.
- Tests that pin exact behaviour (golden outputs, step counts, per-step
  traces) will legitimately break on a behavioural change: **re-derive the
  expected values from the new behaviour, never loosen the assertions to hide
  a regression** (DEVELOPMENT.md §6, §9).
- Keep everything the pinned tests observe **deterministic**: order by stable
  keys, never by pointer address (DEVELOPMENT.md §4.3).
- When comparing (languages, implementations, configurations), control
  confounding factors and compare across several categories of equality
  rather than one number: e.g. time, memory, instructions. Report the
  operating point alongside any aggregate, never the aggregate alone.
- A results file written incrementally must record what actually *completed*,
  never what was *requested*: log the count behind each aggregate, and a null
  (not `0.0`) where a spread cannot be computed.

## Writing

- Use simple language; avoid phrases like "a priori" that only add complexity
  and make text more difficult to read.
- Don't describe obvious or intuitive processes in detail, especially in
  instructions: state what the user needs to do, not a narration of what the
  program will do (e.g. that a program asks for confirmation on the console
  needs no documenting; running it makes that obvious).
- Don't use `—` (em dashes) in any text.
- When creating tables in markdown, pad them with spaces so they appear as
  tables in the raw markdown and are readable as such, and keep every line of
  a table within 140 characters. If a row's text pushes the table over that
  width, rework the responsible rows (shorten their cells, moving detail into
  the surrounding prose); if the content cannot fit, do not use a table (use
  a list or prose instead).
- Refer to an external work (a paper, a spec) by a directly searchable
  shortened title, never by an opaque bibliography key or author-year string
  alone.
