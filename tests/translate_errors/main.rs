//! Front-end validation: malformed `hl` programs are rejected with a
//! `TranslateError` (and a non-empty message) rather than panicking or producing
//! nonsense dialect. These are the kinds of mistakes a user actually makes, so
//! covering the translator's error paths is a sensible regression net for the
//! front-end (and it exercises `hl.rs`'s many `Err(...)` branches).

use formal::hl;

/// Each of these should fail to translate. The tuple's second field documents
/// what is wrong, so a failure here points at which guard stopped working.
const MALFORMED: &[(&str, &str)] = &[
    ("t0 = 1\n    t1 = 2\n", "indentation with no block header"),
    ("missing(7)\nexit(0)\n", "call to an undefined function"),
    ("if t0 ~ t1:\n    t0 = 0\n", "invalid comparison operator"),
    ("while t0:\n    t0 = 0\n", "condition with no comparison"),
    ("v: global zzz\nexit(0)\n", "unknown scalar type"),
    ("v: global [zzz]\nexit(0)\n", "unknown list element type"),
    ("t0 = &\nexit(0)\n", "`&` with no label"),
    ("t0 = &9bad\nexit(0)\n", "`&` with an invalid label"),
    (
        "t0 = csr(nope)\nexit(0)\n",
        "unsupported control/status register",
    ),
    ("t0 = type()\nexit(0)\n", "type() with no label"),
    ("z9 = 0\nexit(0)\n", "assignment to a non-register"),
    ("t0 = t1 + bad\nexit(0)\n", "arithmetic with a bad operand"),
    ("t0 = nonsense\nexit(0)\n", "unrecognised right-hand side"),
    // Definitions and names.
    (
        "9bad: global u8\nexit(0)\n",
        "invalid variable name in a define",
    ),
    (
        "x:\nexit(0)\n",
        "a bare label (empty annotation) is not a statement",
    ),
    ("goto done\nexit(0)\n", "`goto` is not in the language"),
    // Structured-statement headers and conditions.
    (
        "if t0 == t1:\nexit(0)\n",
        "`if` header with no indented block",
    ),
    (
        "if t0 == t1: x\n    t0 = 0\n",
        "trailing text after the `:`",
    ),
    (
        "if 5 == t0:\n    t0 = 0\n",
        "condition left side is not a register",
    ),
    (
        "if t0 == bad:\n    t0 = 0\n",
        "condition right side is not a register",
    ),
    (
        "if t0 < 0:\n    t0 = 0\n",
        "`<` compared against the literal 0",
    ),
    // Stores, loads and arithmetic operands.
    ("t0[0:4] = 5\nexit(0)\n", "store from a non-register"),
    (
        "t0[0:3] = t1\nexit(0)\n",
        "unsupported store width (only 1/2/4)",
    ),
    (
        "t0 = t1[0:5]\nexit(0)\n",
        "unsupported load width (only 1/2/4/8)",
    ),
    ("t0 = type(9bad)\nexit(0)\n", "type() of an invalid label"),
    (
        "t0 = 5 + t1\nexit(0)\n",
        "arithmetic base is not a register",
    ),
    ("t0 = t1 * 3\nexit(0)\n", "`*` with an immediate operand"),
    // Functions: definitions, calls and arguments.
    (
        "def 9bad(x):\n    t0 = 0\n",
        "invalid function name in a `def`",
    ),
    (
        "def f(9bad):\n    t0 = 0\n",
        "invalid parameter name in a `def`",
    ),
    ("def f(x):\nexit(0)\n", "`def` with no indented body"),
    (
        "exit(&foo)\n",
        "a call argument that is neither string, int nor register",
    ),
    (
        "def f(x):\n    f(x)\nf(0)\n",
        "unbounded recursive inlining",
    ),
    // Verifier-only directives and blocks.
    ("forget x9\nexit(0)\n", "`forget` of a non-register"),
    ("asm:\nexit(0)\n", "an empty `asm:` block"),
    ("section 0x100\nexit(0)\n", "a malformed `section`"),
    (
        "section bad 0x200 rw\nexit(0)\n",
        "an invalid `section` bound",
    ),
    (
        "section 0x100 0x200 xyz\nexit(0)\n",
        "invalid `section` permissions",
    ),
];

#[test]
fn translate_rejects_malformed_programs() {
    for (source, why) in MALFORMED {
        match hl::translate(source) {
            Ok(dialect) => {
                panic!("expected a translation error ({why}) for:\n{source}\ngot:\n{dialect}")
            }
            Err(error) => assert!(
                !format!("{error}").is_empty(),
                "the error for ({why}) should render"
            ),
        }
    }
}
