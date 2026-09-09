#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// `return` from an inlined `def`. A `def` has no stack and no `ret`, so a
/// `return` lowers to the assignment to whatever the call site asked for, and
/// the emitted code is exactly what writing the body out by hand emits. The
/// test also covers the canonical non-negative remainder (`slot`, over a
/// negative and a non-negative key) and a polymorphic `def` whose two
/// `if typeof` arms each end in their own `return`.
#[test]
fn def_return() {
    let mut ast = setup_test("def_return/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts: 1,
            }],
        )
        .expect("failed to construct the verifier")
    };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
        indexed,
    } = expect_valid(&trace, result);

    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }

    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
        &indexed,
    );
    bless_asm(
        "def_return/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("def_return", &asm);
    assert_eq!(stdout, "10 6 3", "the three returned values reach stdout");
}

/// The refusals around `return`, pinned by the message rather than merely by
/// failing: several of these programs are wrong in more than one way, so
/// asserting only "it errored" would not show that the intended guard is the
/// one that fired.
#[test]
fn return_refusals_name_the_problem() {
    const CASES: &[(&str, &str)] = &[
        ("return 5\nexit(0)\n", "`return` outside a `def`"),
        (
            "def f(x):\n    return\na0 = f(1)\nexit(0)\n",
            "`return` needs a value",
        ),
        (
            "def f(x):\n    t1 = 0\n    if x == t1:\n        return x\n    return t1\na0 = 3\na1 = f(a0)\nexit(0)\n",
            "would have to jump over the rest of the body",
        ),
        (
            "def f(x):\n    t0 = x\na0 = f(1)\nexit(0)\n",
            "does not return a value",
        ),
        (
            "def f(x):\n    return x\na0 = 1\nt0 = f(a0) + f(a0)\nexit(0)\n",
            "is not a single call",
        ),
        (
            "def type(x):\n    return x\nexit(0)\n",
            "is a builtin, so a `def` cannot take that name",
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
