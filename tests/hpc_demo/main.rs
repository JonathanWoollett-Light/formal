//! A racy program much larger than "Hello World!" - `value` is racily stored,
//! loaded, and proven `== 0` over and over - verified **two ways** from this
//! one self-contained directory:
//!
//! 1. in-process (the reference): infer the type, optimize, lower, and **boot it
//!    in QEMU** (the standard end-to-end test, pinning `emitted.s`);
//! 2. through the **HPC (distributed MPI) model**, confirming the distributed
//!    run infers the identical configuration and accessed byte-ranges.
//!
//! Run it directly:
//!
//! ```text
//! cargo nt hpc_demo
//! ```
//!
//! The model in step 2 is switchable **before running**, without editing the
//! test, via the reusable [`verify_with_model`] helper:
//!
//! ```text
//! FORMAL_TEST_MODEL=sequential cargo nt hpc_demo   # in-process instead of MPI
//! FORMAL_TEST_MODEL=hpc:16     cargo nt hpc_demo   # 16 ranks instead of 8
//! ```
//!
//! The HPC run streams per-rank live progress and a utilisation breakdown to
//! `target/tmp/test-logs/<test>/hpc.log`. Like the QEMU boot tests this is **not**
//! `#[ignore]`d and *fails* (does not skip) if WSL / a system MPI are absent: it
//! builds `--features hpc` in WSL and launches `mpirun`.

#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;

#[test]
fn hpc_demo() {
    let mut ast = setup_test("hpc_demo/dialect.s");
    // Translation pin: the hl source must translate exactly to the stored dialect.
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    let systems = vec![
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 1,
        },
        InnerVerifierConfiguration {
            sections: Default::default(),
            harts: 2,
        },
    ];

    // (1) In-process reference: infer the configuration, then optimize, lower, and
    // boot. `verify_inferred` (the parallel inner pool) yields the same
    // `ValidPathResult` as the sequential oracle - pinned by
    // `tests/parallel_oracle_crosscheck` - without building this large program's
    // multi-hundred-thousand-step trace.
    let result = unsafe { verify_inferred(ast, &systems) }.expect("verification failed");
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    } = match result {
        ExplorePathResult::Valid(valid) => valid,
        _ => panic!("hpc_demo: expected a valid path"),
    };

    // The inferred type (word-sized racy accesses fix `value: u32`).
    assert_eq!(
        configuration,
        TypeConfiguration(
            vec![(Label::from("value"), (LabelLocality::Global, Type::U32))]
                .into_iter()
                .collect()
        )
    );
    // It accesses exactly the four bytes of `value` at runtime.
    assert_eq!(
        accessed,
        vec![(Label::from("value"), [(0, 4)].into_iter().collect())]
            .into_iter()
            .collect()
    );

    // Dead-code/branch elimination, then pin the lowered program and boot it.
    unsafe {
        remove_untouched(&mut ast, &touched);
        remove_branches(&mut ast, &jumped);
    }
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm("hpc_demo/emitted.s", asm, include_str!("emitted.s"));
    let serial = unsafe {
        run_program(
            "hpc_demo",
            ast,
            &configuration,
            &accessed,
            &transitions,
            &uncompactable,
            &pinned_nodes,
        )
    };
    assert_eq!(serial, "", "hpc_demo produces no UART output");

    // (2) The HPC model: verify the SAME program distributed (work-stealing under
    // `mpirun`) and confirm it infers the identical configuration + accessed
    // ranges as the in-process reference above.
    let outcome = verify_with_model("hpc_demo/dialect.s", &[1, 2], Model::Hpc { ranks: 8 });
    eprintln!(
        "[{}] configuration={} touched={} accessed={}  (detail log: {})",
        outcome.model, outcome.configuration, outcome.touched, outcome.accessed, outcome.log,
    );
    assert!(
        outcome.configuration.contains("value:Gu32"),
        "HPC model inferred {} (see {})",
        outcome.configuration,
        outcome.log,
    );
    assert!(
        outcome.accessed.contains("\"value\": {(0, 4)}"),
        "HPC model accessed {} (see {})",
        outcome.accessed,
        outcome.log,
    );
}
