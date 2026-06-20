#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// A fast minimal 3-hart smoke test (the cheap counterpart of the booting
/// `fannkuch_v2`): a leader/worker program verifies under a **3-hart**
/// configuration. The leader (`mhartid == 0`) proves a trivial fact; every other
/// hart skips to the shared inline-asm `wfi`. No shared memory, so the harts are
/// independent (non-racy) and the interleaving collapses -- it verifies in
/// milliseconds, exercising the symbolic hart-id model and the 3-hart front
/// tracking without the leader/worker front-search worst case.
#[test]
fn three_harts() {
    let ast = setup_test("three_harts/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts: 3,
            }],
        )
        .expect("failed to construct the verifier")
    };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let _ = expect_valid(&trace, result);
}
