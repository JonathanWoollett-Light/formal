#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// An element index **past the end** of the pointee. `arr` has two elements, so
/// `arr[2]` describes memory the variable does not have: the element-granular
/// form of an access past a label, and rejected the same way (`Invalid`, at
/// compile time, never a runtime check).
#[test]
fn index_past_the_end_is_invalid() {
    let ast = setup_test("element_refusals/out_of_bounds.s");
    let translated =
        hl::translate(include_str!("out_of_bounds.hl")).expect("hl translation failed");
    assert_eq!(
        normalize(translated),
        normalize(include_str!("out_of_bounds.s"))
    );

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

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (element index past the end of `arr`), got {outcome:?}"
    );
    assert!(!trace.is_empty(), "expected a non-empty trace");
}

/// An element index through a **raw address**. A `#@` region is bytes with no
/// element type, so there is nothing to count elements of: the verifier refuses
/// the program with an error naming the byte-slice form that fits such memory,
/// rather than guessing a width or accepting it.
#[test]
fn index_through_a_raw_address_is_refused() {
    let ast = setup_test("element_refusals/raw_address.s");
    let translated = hl::translate(include_str!("raw_address.hl")).expect("hl translation failed");
    assert_eq!(
        normalize(translated),
        normalize(include_str!("raw_address.s"))
    );

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
    let (_trace, result) = unsafe { trace_valid_path(explorerer) };

    let error = result.expect_err("expected a refusal, not a valid path");
    let CompilerError::Unsupported(message) = &error else {
        panic!("expected CompilerError::Unsupported, got {error:?}");
    };
    assert!(
        message.contains("element index through the raw address") && message.contains("p[a:b]"),
        "the refusal should name the byte-slice form: {message}"
    );
}
