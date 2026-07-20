//! The `hl` type grammar: run-length list types. A run is `<scalar>*<count>`
//! with `*` binding tightly; runs are comma-separated inside the brackets, so
//! `[u8*13]` replaces `[u8]*13` and heterogeneous layouts compose:
//! `[u8*2, u16*2, u8*3]`. Every form still expands to the dialect's flat
//! space-separated list, so nothing downstream of the front-end changes, and
//! the legacy outer `*n` suffix keeps its cycling semantics (`[u8, u16]*2` =
//! `[u8 u16 u8 u16]`), which makes `[u8]*13` and `[u8*13]` the same type.

use formal::hl;

/// Translates one define and returns its `#$` dialect line.
fn define_line(program: &str) -> String {
    let out = hl::translate(program).expect("translation should succeed");
    out.lines()
        .find(|l| l.trim_start().starts_with("#$"))
        .expect("expected a #$ define line")
        .trim()
        .to_string()
}

#[test]
fn run_length_types_expand_flat() {
    // A single run.
    assert_eq!(
        define_line("x: thread [u8*3]\nexit(0)\n"),
        "#$ x thread [u8 u8 u8]"
    );
    // A heterogeneous run-length layout.
    assert_eq!(
        define_line("p: global [u8*2, u16*2, u8*3]\nexit(0)\n"),
        "#$ p global [u8 u8 u16 u16 u8 u8 u8]"
    );
    // Runs mix with plain elements.
    assert_eq!(
        define_line("q: _ [u32, u8*2]\nexit(0)\n"),
        "#$ q _ [u32 u8 u8]"
    );
    // The legacy outer suffix still cycles the whole element list.
    assert_eq!(
        define_line("w: _ [u8, u16]*2\nexit(0)\n"),
        "#$ w _ [u8 u16 u8 u16]"
    );
    // Legacy and run forms agree: `[u8]*13` == `[u8*13]`.
    assert_eq!(
        define_line("a: _ [u8]*13\nexit(0)\n"),
        define_line("a: _ [u8*13]\nexit(0)\n")
    );
    // The outer suffix composes with runs (cycling the expanded elements).
    assert_eq!(
        define_line("y: _ [u8*2]*3\nexit(0)\n"),
        "#$ y _ [u8 u8 u8 u8 u8 u8]"
    );
}
