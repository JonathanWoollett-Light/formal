#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// A store that overruns its `#@` region: the region is 2 bytes but the `sw`
/// needs 4. The bounds check requires the access's bytes to fit within the
/// declared region (`required_size <= size`), so no region covers the store and
/// the program is rejected as `Invalid`. (This pins the *direction* of the
/// bounds comparison: with the operands swapped, accepting regions *smaller*
/// than the access, this program would wrongly verify.)
#[test]
fn store_overrunning_its_region_is_invalid() {
    let ast = setup_test("region_overrun/dialect.s");
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
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

    // Exploration up to the offending store is ordinary...
    let expected_trace = [
        "h0/1 | #@ 0x80100000 0x80100002 rw | Config: [] | q1 t1 j0",
        "h0/1 | li t0, 0x80100000 | Config: [] | q1 t2 j0",
        "h0/1 | li t1, 42 | Config: [] | q1 t3 j0",
    ];
    assert_trace(&trace, &expected_trace);

    // ...then the `sw` needs more bytes than the region declares: with no
    // variables to re-type, backtracking exhausts and the program is rejected.
    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (store overruns its region), got {outcome:?}"
    );
}
