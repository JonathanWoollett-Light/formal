mod common;

use common::*;
use formal::*;

/// Two `#$` defines that disagree about a variable's type. The first configures
/// `value: (Global, U8)`; the second is *checked* against that configuration,
/// fails, and — since the annotation restricted the search to exactly one
/// candidate — backtracking exhausts immediately: the program has no valid
/// configuration.
#[test]
fn conflicting_defines_are_invalid() {
    let ast = setup_test("conflicting_defines");

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

    // The first define configures the variable; the second contradicts it and
    // resets the configuration, and with no other candidate to try (the
    // annotation admits exactly one) exploration terminates.
    let expected_trace = [
        "h0/1 | #$ value global u8 | Config: [value:Gu8,] | q1 t1 j0",
        "h0/1 | #$ value global u16 | Config: [] | q1 t2 j0",
    ];
    assert_trace(&trace, &expected_trace);

    // ...and the second contradicts it.
    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (conflicting defines), got {outcome:?}"
    );
}
