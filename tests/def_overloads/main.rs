#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::hl;

/// Typed, destructuring overloads of one `def` name, resolved at translate
/// time by shape, arity and each argument's shape: a register or an integer
/// literal is a scalar; a variable name or a string literal is an array, whose
/// element list the front-end reads back from the `#$` define it already
/// emitted. An array pattern is either spelled out in full (`[i32, i32]`,
/// checked element by element, so `data` and `pair` below take different
/// overloads by their declared element types) or `[..]`, any array. `f(a, b)`
/// is `f([a, b])`, in a call and in a header alike. Only the taken overload's
/// body is translated, bound by the same whole-token substitution as a
/// one-parameter `def`, so every call lowers to exactly the lines its body was
/// going to emit anyway.
#[test]
fn overloads_resolve_by_shape_arity_and_elements() {
    const PROGRAM: &str = "\
data: [u8]*2
pair: [i32]*2
def shape(x: i64):
    return x + x
def shape(x: [u8*2]):
    return &x
def shape(x: [i32, i32]):
    t0 = &x
    return t0[1]
def shape([lo, hi]: [i64, i64]):
    return lo - hi
def shape([s, n]: [[..], _]):
    t1 = &s
    return t1 + n
def shape(a, b, c):
    return a + c
def g(a: i64, b: [..]):
    t2 = &b
    return t2 + a
a0 = 3
a1 = shape(a0)
a2 = shape(data)
a3 = shape([a1, a0])
a4 = shape([data, a0])
a5 = shape([\"hi\", a0])
a6 = shape(pair)
a7 = shape(a0, a1, a2)
t3 = g(a0, data)
exit(0)
";
    // No `\` after the opening quote: a backslash-newline would strip the
    // first line's indentation, which is part of the canonical form.
    const DIALECT: &str = "    #$ data thread [u8 u8]
    #$ pair thread [i32 i32]
    li a0, 3
    add a1, a0, a0
    la a2, data
    sub a3, a1, a0
    la t1, data
    add a4, t1, a0
    #$ __str0 thread [u8 u8 u8]
    la t0, __str0
    li t1, 104
    sb t1, 0(t0)
    li t1, 105
    sb t1, 1(t0)
    li t1, 0
    sb t1, 2(t0)
    la t1, __str0
    add a5, t1, a0
    la t0, pair
    #[ a6, 1(t0)
    add a7, a0, a2
    la t2, data
    add t3, t2, a0
    li a0, 0
    li a7, 93
    ecall
    #?
";
    let translated = hl::translate(PROGRAM).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(DIALECT));
}

/// Each refusal is pinned by its message, so a failure shows which guard fired
/// (several of these programs are wrong in more than one way).
#[test]
fn overload_refusals_name_the_problem() {
    const CASES: &[(&str, &str)] = &[
        (
            "def f(x: i64):\n    t0 = x\ndef f(y):\n    t0 = y\nexit(0)\n",
            "overlaps `def f(x: i64)`",
        ),
        ("def print(x):\n    t0 = x\nexit(0)\n", "std/std.hl line"),
        (
            "def f(x: i64):\n    return x\na0 = f(\"s\")\nexit(0)\n",
            "no overload of `f` takes",
        ),
        (
            "def f([a, b]):\n    return a + b\na0 = 1\na1 = f(a0)\nexit(0)\n",
            "no overload of `f` takes",
        ),
        (
            "def f([a, b]: [i64]):\n    return a + b\nexit(0)\n",
            "names 2 parameters but its type",
        ),
        (
            "def f([t0, x]):\n    t1 = x\nexit(0)\n",
            "is a reserved word",
        ),
        ("def f([a, a]):\n    t0 = a\nexit(0)\n", "is named twice"),
        (
            "def f(buf):\n    buf: [u8*4]\nexit(0)\n",
            "is also defined in the body",
        ),
        (
            "def f([a, b]):\n    t2 = &a\nf([\"s\", t0])\nexit(0)\n",
            "clobbers them",
        ),
        (
            "def f(x):\n    return x\n    t0 = 1\na0 = f(1)\nexit(0)\n",
            "must be the last statement",
        ),
        (
            "def f(x: [..]):\n    t0 = 1\na0 = f(\"s\")\nexit(0)\n",
            "does not return a value",
        ),
        (
            "def f(x):\n    if typeof x == _:\n        t0 = x\nf(1)\nexit(0)\n",
            "is always taken",
        ),
        (
            "arr: [u8*2]\nt0 = arr[0]\nexit(0)\n",
            "take its address first",
        ),
        (
            "def f(x):\n    t0 = x\nf(u8)\nexit(0)\n",
            "is a reserved word",
        ),
        (
            "def f(x):\n    t0 = x\nf([1])\nexit(0)\n",
            "needs at least two elements",
        ),
        (
            "def f([x]):\n    t0 = x\nexit(0)\n",
            "one-name tuple pattern",
        ),
        // A spelled-out array pattern is checked, so the variable must be
        // defined above the call for the front-end to see its elements.
        (
            "def f(x: [i32, i32]):\n    t0 = &x\nf(nums)\nexit(0)\n",
            "has no define before this call",
        ),
        // `..` means the whole array or nothing.
        (
            "def f(x: [u8, ..]):\n    t0 = &x\nexit(0)\n",
            "either list every element or write `[..]`",
        ),
        // Wrong length is a plain miss, reported with the elements seen.
        (
            "d: [u8]*3\ndef f(x: [u8, u8]):\n    t0 = &x\nf(d)\nexit(0)\n",
            "an array of [u8, u8, u8]",
        ),
        // The comma spelling is the same tuple: one argument does not fit it.
        (
            "def f(a, b):\n    return a + b\na0 = 1\na1 = f(a0)\nexit(0)\n",
            "no overload of `f` takes",
        ),
    ];
    for (source, expected) in CASES {
        let error =
            hl::translate(source).expect_err(&format!("this should not translate:\n{source}"));
        assert!(
            error.message.contains(expected),
            "expected a message containing `{expected}`, got `{}` for:\n{source}",
            error.message
        );
    }
}

/// A parameter name inside a string literal is text, not a token: the
/// substitution must leave it alone, or `def f(n): print("\\n")` would
/// rewrite the escape.
#[test]
fn substitution_leaves_string_literals_alone() {
    const PROGRAM: &str = "\
def tag(n):
    print(\"n=\")
    print(n)
a0 = 7
tag(a0)
exit(0)
";
    let translated = hl::translate(PROGRAM).expect("hl translation failed");
    // The string's bytes are `n` (110) and `=` (61): the `n` survived.
    assert!(
        translated.contains("li t1, 110"),
        "the `n` inside the string literal must not be substituted:\n{translated}"
    );
}
