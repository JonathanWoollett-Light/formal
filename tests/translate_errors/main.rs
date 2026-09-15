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
    (
        "v: global [u8 * 3]\nexit(0)\n",
        "run repetition must bind tightly (`u8*3`, not `u8 * 3`)",
    ),
    ("v: global [u8*0]\nexit(0)\n", "zero run repetition"),
    ("v: global [u8*x]\nexit(0)\n", "non-numeric run repetition"),
    (
        "v: global [u8*+3]\nexit(0)\n",
        "signed run count (digits only)",
    ),
    (
        "v: global [u8]*+13\nexit(0)\n",
        "signed legacy count (digits only)",
    ),
    (
        "v: global [u8*16777217]\nexit(0)\n",
        "run count over the expansion cap",
    ),
    (
        "v: global [u8, u8]*9223372036854775807\nexit(0)\n",
        "outer repetition overflowing the expansion cap",
    ),
    ("v: global [*3]\nexit(0)\n", "a run with no element type"),
    ("v: global [zzz*3]\nexit(0)\n", "unknown run element type"),
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
    (
        "v: glbal u32\nexit(0)\n",
        "a misspelt locality reads as part of the type, and is named as such",
    ),
    (
        "return 5\nexit(0)\n",
        "`return` outside a `def`",
    ),
    (
        "def f(x):\n    return\na0 = f(1)\nexit(0)\n",
        "`return` with no value",
    ),
    (
        "def f(x):\n    t1 = 0\n    if x == t1:\n        return x\n    return t1\na0 = 3\na1 = f(a0)\nexit(0)\n",
        "an early `return` inside an `if` needs a jump the language does not have",
    ),
    (
        "def f(x):\n    t1 = 0\n    while x != t1:\n        return x\n    return t1\na0 = 3\na1 = f(a0)\nexit(0)\n",
        "an early `return` inside a `while`",
    ),
    (
        "def f(x):\n    t0 = x\na0 = f(1)\nexit(0)\n",
        "assigning from a `def` that returns nothing",
    ),
    (
        "def f(x):\n    return nonsense\nf(1)\nexit(0)\n",
        "a bad expression in a dropped `return` is still checked",
    ),
    (
        "def f(x):\n    return x\na0 = 1\nt0 = f(a0) + f(a0)\nexit(0)\n",
        "a call may not be part of a larger expression",
    ),
    (
        "def type(x):\n    return x\nexit(0)\n",
        "a `def` may not shadow the builtin `type`",
    ),
    (
        "def csr(x):\n    return x\nexit(0)\n",
        "a `def` may not shadow the builtin `csr`",
    ),
    // Overloads: headers and calls.
    (
        "def f(x: u9):\n    t0 = x\nf(1)\nexit(0)\n",
        "invalid parameter type",
    ),
    (
        "def f([a, a]):\n    t0 = a\nf([1, 2])\nexit(0)\n",
        "a parameter named twice",
    ),
    (
        "def f([t0, x]):\n    t1 = x\nf([1, 2])\nexit(0)\n",
        "a register as a parameter name",
    ),
    (
        "def f(u8):\n    t0 = 1\nf(1)\nexit(0)\n",
        "a type name as a parameter name",
    ),
    (
        "def f(_):\n    t0 = 1\nf(1)\nexit(0)\n",
        "`_` as a parameter name",
    ),
    (
        "def f(buf):\n    buf: [u8*4]\nf(1)\nexit(0)\n",
        "a parameter that the body also defines",
    ),
    (
        "def f([a, b]: [i64]):\n    t0 = a\nf([1, 2])\nexit(0)\n",
        "tuple type shorter than the pattern",
    ),
    (
        "def f([a, b]: i64):\n    t0 = a\nf([1, 2])\nexit(0)\n",
        "a tuple pattern with a non-tuple type",
    ),
    (
        "def f([x]):\n    t0 = x\nf([1])\nexit(0)\n",
        "a one-name tuple pattern",
    ),
    (
        "def f(x: i64):\n    t0 = x\ndef f(y):\n    t0 = y\nexit(0)\n",
        "overlapping overloads",
    ),
    (
        "def print(x):\n    t0 = x\nexit(0)\n",
        "a user `def` overlapping a std one",
    ),
    (
        "def f(x: i64):\n    t0 = x\nf(\"s\")\nexit(0)\n",
        "a string where a scalar is typed",
    ),
    (
        "def f(x: [u8]):\n    t0 = &x\nf(5)\nexit(0)\n",
        "an integer where an array is typed",
    ),
    (
        "def f([a, b]):\n    t0 = a\nf(1)\nexit(0)\n",
        "one argument to a tuple pattern",
    ),
    (
        "def f(x):\n    t0 = x\nf([1])\nexit(0)\n",
        "a one-element tuple argument",
    ),
    (
        "def f([a, b]):\n    t2 = &a\nf([\"s\", t0])\nexit(0)\n",
        "a string next to t0 in a tuple",
    ),
    (
        "def f(x):\n    t0 = x\nf(u8)\nexit(0)\n",
        "a reserved word as an argument",
    ),
    (
        "def f([a, b]):\n    t0 = a\nf([1, 2)\nexit(0)\n",
        "an unterminated tuple argument",
    ),
    (
        "def f(x):\n    return x\nx = f(1)\nexit(0)\n",
        "a call assigned to a non-register",
    ),
    (
        "def f(x):\n    return x\n    t0 = 1\na0 = f(1)\nexit(0)\n",
        "a statement after `return`",
    ),
    (
        "def f(x):\n    if typeof x == _:\n        t0 = x\nf(1)\nexit(0)\n",
        "`_` in an `if typeof`",
    ),
    (
        "arr: [u8*2]\nt0 = arr[0]\nexit(0)\n",
        "indexing a variable on the load side",
    ),
    // Array patterns and the comma spelling.
    (
        "def f(x: [i32, i32]):\n    t0 = &x\nf(nums)\nexit(0)\n",
        "a spelled-out array pattern against an undefined variable",
    ),
    (
        "def f(x: [u8, ..]):\n    t0 = &x\nexit(0)\n",
        "`..` inside a list: every element or `[..]`",
    ),
    (
        "d: [u8]*3\ndef f(x: [u8, u8]):\n    t0 = &x\nf(d)\nexit(0)\n",
        "a spelled-out array pattern of the wrong length",
    ),
    (
        "v: global _\ndef f(x: [u32]):\n    t0 = &x\nf(v)\nexit(0)\n",
        "a spelled-out array pattern against an inferred type",
    ),
    (
        "def f(a, b):\n    return a + b\na0 = 1\na1 = f(a0)\nexit(0)\n",
        "one argument to a comma-spelled tuple",
    ),
    (
        "def f(a, a):\n    return a\nexit(0)\n",
        "a repeated name in the comma spelling",
    ),
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
    // Element indexing: the index must be a constant the directive can carry
    // (the pointee's type, and so the access width, is the verifier's to
    // resolve, but the index is the source's to state).
    (
        "t0[t1] = t2\nexit(0)\n",
        "a runtime index is not supported yet",
    ),
    ("t0 = t1[a0]\nexit(0)\n", "a runtime index on the load side"),
    ("t0[-1] = t1\nexit(0)\n", "a negative element index"),
    ("t0[] = t1\nexit(0)\n", "an empty index"),
    ("t0[x] = t1\nexit(0)\n", "an index that is not an integer"),
    (
        "arr[0] = t1\nexit(0)\n",
        "indexing a variable instead of a register",
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
