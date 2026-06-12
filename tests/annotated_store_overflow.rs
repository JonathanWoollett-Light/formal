mod common;

use common::*;
use formal::*;

/// A 4-byte `sw` into a variable annotated `u8`. The annotation removes the
/// type search (only `(Global, U8)` is admissible), the store cannot fit in one
/// byte, and the program is rejected as `Invalid` — the labelled-access bounds
/// check with no remaining candidates to back off to.
#[test]
fn oversized_store_into_annotated_type_is_invalid() {
    let ast = setup_test("annotated_store_overflow");

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

    let expected_trace = [
        "h0/1 | #$ value global u8 | Config: [value:Gu8,] | q1 t1 j0",
        "h0/1 | la t0, value | Config: [value:Gu8,] | q1 t2 j0",
        "h0/1 | li t1, 0 | Config: [value:Gu8,] | q1 t3 j0",
        // The failing store resets the configuration; with no remaining
        // candidate for the annotated variable, the re-encounter terminates.
        "h0/1 | sw t1, 0(t0) | Config: [] | q1 t4 j0",
    ];
    assert_trace(&trace, &expected_trace);

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (4-byte store into u8), got {outcome:?}"
    );
}
