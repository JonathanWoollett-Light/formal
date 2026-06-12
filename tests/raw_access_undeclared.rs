mod common;

use common::*;
use formal::*;

/// A raw-address load with no `#@` region (and no system-configured section)
/// describing it. Every memory access must be verifiable as safe — through a
/// symbolic variable (whose storage codegen places in `.data`/`.bss`) or a
/// described raw region — so this program has no valid configuration: the
/// verifier rejects it as `Invalid` (rather than erroring or accepting it).
#[test]
fn raw_access_outside_any_region_is_invalid() {
    let ast = setup_test("raw_access_undeclared");

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

    // Exploration up to the offending load is ordinary...
    let expected_trace = [
        "h0/1 | li t0, 0x100 | Config: [] | q1 t1 j0",
        "h0/1 | li t2, 0 | Config: [] | q1 t2 j0",
    ];
    assert_trace(&trace, &expected_trace);

    // ...then the `lw` reads memory no `#@` region describes: with no variables
    // to re-type, backtracking exhausts immediately and the program is rejected.
    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (raw access outside any region), got {outcome:?}"
    );
}
