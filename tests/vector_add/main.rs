#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **SIMD vector add via the RISC-V V extension.** An `asm:` block sets the vector
/// length to 4, splats 1 and 2 into `v0`/`v1`, adds them lane-wise into `v2`, and
/// extracts lane 0 into `a0`; the program prints it (`3`). The verifier models a
/// vector register as a `MemoryValue::List` of lanes and `vl` as a tracked
/// register, computing the lane-wise add concretely; QEMU (`qemu-riscv64`, which
/// runs the V extension by default) executes the real vector instructions. The
/// toolchain assembles them with `-march=rv64gcv`. This is the minimal end-to-end
/// proof of the vector instruction support (`vsetivli`, `vmv.v.i`, `vadd.vv`,
/// `vmv.x.s`); vector loads/stores and `vrgather` are a further step.
#[test]
fn vector_add() {
    let mut ast = setup_test("vector_add/dialect.s");
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
    let ValidPathResult {
        configuration,
        touched,
        jumped,
        accessed,
        transitions,
        uncompactable,
        pinned_nodes,
    } = expect_valid(&trace, result);

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
    bless_asm(
        "vector_add/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("vector_add", &asm);
    assert_eq!(stdout, "3", "1 + 2 lane-wise, lane 0 extracted");
}
