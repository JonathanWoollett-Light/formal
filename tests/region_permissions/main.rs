#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

fn verify(asset: &str) -> (Vec<String>, Result<ExplorePathResult, CompilerError>) {
    let ast = setup_test(asset);
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
    unsafe { trace_valid_path(explorerer) }
}

/// A store into a `#@ … r` (read-only) region: the section covers the address,
/// but writing needs `w`, so the access is unverifiable and the program is
/// rejected as `Invalid`.
#[test]
fn write_to_read_only_region_is_invalid() {
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
    let translated = hl::translate(include_str!("read_only.hl")).expect("hl translation failed");
    assert_eq!(
        normalize(translated),
        normalize(include_str!("read_only.s"))
    );

    let (trace, result) = verify("region_permissions/read_only.s");

    let expected_trace = [
        "h0/1 | #@ 0x80100000 0x80100004 r | Config: [] | q1 t1 j0",
        "h0/1 | li t0, 0x80100000 | Config: [] | q1 t2 j0",
        "h0/1 | li t1, 42 | Config: [] | q1 t3 j0",
    ];
    assert_trace(&trace, &expected_trace);

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (store into read-only region), got {outcome:?}"
    );
}

/// A load from a `#@ … w` (write-only) region: reading needs `r`, so the access
/// is unverifiable and the program is rejected as `Invalid`.
#[test]
fn read_from_write_only_region_is_invalid() {
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
    let translated = hl::translate(include_str!("write_only.hl")).expect("hl translation failed");
    assert_eq!(
        normalize(translated),
        normalize(include_str!("write_only.s"))
    );

    let (trace, result) = verify("region_permissions/write_only.s");

    let expected_trace = [
        "h0/1 | #@ 0x80100000 0x80100004 w | Config: [] | q1 t1 j0",
        "h0/1 | li t0, 0x80100000 | Config: [] | q1 t2 j0",
        "h0/1 | li t5, 0 | Config: [] | q1 t3 j0",
    ];
    assert_trace(&trace, &expected_trace);

    let outcome = result.expect("expected a terminal outcome, not a compiler error");
    assert!(
        matches!(outcome, ExplorePathResult::Invalid),
        "expected Invalid (load from write-only region), got {outcome:?}"
    );
}
