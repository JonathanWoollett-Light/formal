#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **Lock-free work claiming.** Two harts atomically fetch-add a zero-init global
/// `rank` counter (`amoadd.w`) to each claim a unique rank; the verifier proves
/// every claim is in range (`< 2`) across all 2-hart interleavings. This is the
/// racy atomic primitive (modeled, not opaque) on top of zero-init globals -- the
/// basis for splitting fannkuch across harts with no start barrier.
#[test]
fn atomic_claim() {
    let ast = setup_test("atomic_claim/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: Default::default(),
                harts: 2,
            }],
        )
        .expect("failed to construct the verifier")
    };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let _ = expect_valid(&trace, result);
    eprintln!("atomic_claim: {} steps", trace.len());
}
