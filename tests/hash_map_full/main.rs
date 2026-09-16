#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// The std hash map's refusal of a table too small for its keys. Capacity 8 is
/// a single window and nine distinct keys are inserted: the ninth finds no key
/// and no EMPTY or DELETED byte, so `hm_insert` reaches its `fail` and the
/// program is `Invalid` at compile time (never a runtime check). With no
/// allocation there is no growth; this refusal is what stands in for it.
#[test]
fn hash_map_full() {
    let ast = setup_test("hash_map_full/dialect.s");
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

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (the ninth insert reaches hm_insert's `fail`), got {outcome:?}"
    );
    assert!(!trace.is_empty(), "expected a non-empty trace");
}
