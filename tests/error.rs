mod common;

use common::*;
use formal::*;

/// When the verifier hits a construct it cannot handle (here, a `.global`
/// directive — programs have no explicit entry point, so the verifier does not
/// model it), it must return a [`CompilerError`] instead of panicking, so the
/// test gets both the error *and* the trace of steps leading up to it rather
/// than a dead test binary.
#[test]
fn unsupported_construct_returns_error_with_trace() {
    let ast = setup_test("error");

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

    // The verifier reports the unsupported construct as a recoverable error...
    let error = result.expect_err("expected an unsupported-construct error, not a valid path");
    assert!(
        matches!(error, CompilerError::Unsupported(_)),
        "expected CompilerError::Unsupported, got {error:?}"
    );

    // ...and the trace (including the failing step) is available for diagnostics,
    // so we can see exactly where exploration could not continue.
    assert!(!trace.is_empty(), "expected a non-empty trace");
    let last = trace.last().expect("non-empty trace");
    assert!(
        last.contains(".global _start") && last.contains("error"),
        "expected the final trace line to be the failing directive; got: {last}"
    );
}
