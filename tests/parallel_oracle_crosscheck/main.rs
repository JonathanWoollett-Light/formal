//! Phase 0e: cross-check the fixed-configuration inner search
//! ([`verify_configuration`]) against the sequential [`Explorerer`] oracle.
//!
//! For a **fully annotated** program the oracle never backtracks over candidate
//! types, so its grow-only outputs (`touched`/`jumped`/`accessed`/`transitions`/
//! `uncompactable`/`pinned_nodes`) are exactly one configuration's. Running
//! `verify_configuration` on the oracle's winning configuration must therefore
//! reproduce the identical [`ValidPathResult`]. Both runs explore the same
//! (immutable) AST, so the pointer-keyed outputs are directly comparable.
//!
//! This is the regression net that replaces the deleted per-step trace pins for
//! the parallel path: it asserts *output-level* equivalence, which is what the
//! distributed design guarantees (and all codegen downstream consumes).

#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

fn systems() -> Vec<InnerVerifierConfiguration> {
    vec![
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 1,
        },
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 2,
        },
    ]
}

/// The fixed-config inner search reproduces the oracle's outputs exactly on an
/// annotated program (no outer backtracking, so the oracle explores one config).
#[test]
fn fixed_config_matches_oracle_annotated() {
    let ast = setup_test("racy_store_annotated/dialect.s");
    let sys = systems();

    // Oracle: the full sequential explorer (outer type search + inner search).
    let explorerer = unsafe { Explorerer::new(ast, &sys).expect("construct verifier") };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let oracle = expect_valid(&trace, result);

    // Fixed-config inner search on the oracle's winning configuration.
    let result = unsafe { verify_configuration(ast, &sys, &oracle.configuration) }
        .expect("verify_configuration returned a compiler error");
    let fixed = match result {
        ExplorePathResult::Valid(valid) => valid,
        ExplorePathResult::Invalid => {
            panic!("verify_configuration rejected a configuration the oracle accepted")
        }
        ExplorePathResult::Continue(_) => {
            panic!("verify_configuration returned Continue instead of a terminal")
        }
    };

    // Output-level equivalence: every grow-only accumulator and the winning
    // configuration must match the oracle bit for bit.
    assert_eq!(fixed.configuration, oracle.configuration, "configuration");
    assert_eq!(fixed.touched, oracle.touched, "touched");
    assert_eq!(fixed.jumped, oracle.jumped, "jumped");
    assert_eq!(fixed.accessed, oracle.accessed, "accessed");
    assert_eq!(fixed.transitions, oracle.transitions, "transitions");
    assert_eq!(fixed.uncompactable, oracle.uncompactable, "uncompactable");
    assert_eq!(fixed.pinned_nodes, oracle.pinned_nodes, "pinned_nodes");
}

/// A configuration that conflicts with the program (here `value` forced to `u8`
/// while the program annotates and stores it as `u32`) must be rejected as
/// `Invalid` for that configuration, never accepted.
#[test]
fn fixed_config_wrong_type_is_invalid() {
    let ast = setup_test("racy_store_annotated/dialect.s");
    let sys = systems();

    let wrong = TypeConfiguration(
        vec![(Label::from("value"), (LabelLocality::Global, Type::U8))]
            .into_iter()
            .collect(),
    );

    let result = unsafe { verify_configuration(ast, &sys, &wrong) }
        .expect("verify_configuration returned a compiler error");
    assert!(
        matches!(result, ExplorePathResult::Invalid),
        "a u8 configuration must be invalid for a program that stores u32 into `value`"
    );
}

fn cfg(locality: LabelLocality, ty: Type) -> TypeConfiguration {
    TypeConfiguration(
        vec![(Label::from("value"), (locality, ty))]
            .into_iter()
            .collect(),
    )
}

/// The parallel outer sweep verifies candidates concurrently (rayon) over the
/// shared immutable AST and returns the valid one, with outputs matching the
/// oracle. A wrong (`u8`) candidate is included to prove the sweep selects the
/// valid configuration rather than the first.
#[test]
fn parallel_sweep_picks_valid_config() {
    let ast = setup_test("racy_store_annotated/dialect.s");
    let sys = systems();

    let explorerer = unsafe { Explorerer::new(ast, &sys).expect("construct verifier") };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let oracle = expect_valid(&trace, result);

    // Wrong candidate first, valid candidate second: selection must be by
    // validity (and rank), not position.
    let candidates = vec![
        cfg(LabelLocality::Global, Type::U8),
        cfg(LabelLocality::Global, Type::U32),
    ];
    let result = unsafe { verify_sweep(ast, &sys, &candidates) }.expect("sweep errored");
    let valid = match result {
        ExplorePathResult::Valid(valid) => valid,
        _ => panic!("the parallel sweep failed to find the valid configuration"),
    };

    assert_eq!(valid.configuration, oracle.configuration, "configuration");
    assert_eq!(valid.touched, oracle.touched, "touched");
    assert_eq!(valid.jumped, oracle.jumped, "jumped");
    assert_eq!(valid.accessed, oracle.accessed, "accessed");
    assert_eq!(valid.transitions, oracle.transitions, "transitions");
    assert_eq!(valid.uncompactable, oracle.uncompactable, "uncompactable");
    assert_eq!(valid.pinned_nodes, oracle.pinned_nodes, "pinned_nodes");
}

/// A sweep whose every candidate is invalid yields `Invalid`.
#[test]
fn parallel_sweep_all_invalid_is_invalid() {
    let ast = setup_test("racy_store_annotated/dialect.s");
    let sys = systems();
    let candidates = vec![cfg(LabelLocality::Global, Type::U8)];
    let result = unsafe { verify_sweep(ast, &sys, &candidates) }.expect("sweep errored");
    assert!(matches!(result, ExplorePathResult::Invalid));
}
