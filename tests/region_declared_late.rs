mod common;

use common::*;
use formal::*;

/// The store precedes its `#@` declaration in program order. Regions take
/// effect when *executed* (declare-before-use — an allocator declares each
/// allocation before handing out its pointer), so at the store nothing
/// describes the address and the program is rejected as `Invalid`.
#[test]
fn access_before_declaration_is_invalid() {
    let ast = setup_test("region_declared_late");

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
        "h0/1 | li t0, 0x80100000 | Config: [] | q1 t1 j0",
        "h0/1 | li t1, 42 | Config: [] | q1 t2 j0",
    ];
    assert_trace(&trace, &expected_trace);

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (access before region declaration), got {outcome:?}"
    );
}
