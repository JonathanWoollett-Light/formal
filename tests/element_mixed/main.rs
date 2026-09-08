#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// **A mixed-shape list**, `[u8*2, i16*1, u32*1, i32*1]`: five elements of
/// three widths and both signednesses at byte offsets 0, 1, 2, 4 and 8.
///
/// Two things a byte slice cannot state, both pinned here. Which element `k`
/// names depends on where the pointer sits, so the verifier walks the type from
/// the pointer's exact offset rather than multiplying an index by a stride
/// (elements 0/2/3/4 are bytes 0/2/4/8). And the resolution carries the
/// element's *type*, so each load extends the way the value was modelled:
/// `rec[0]` is a `u8` and reads back as 200 rather than the -56 a sign-extending
/// load would give, while `rec[2]`/`rec[4]` keep their negatives. The `require`s
/// prove that of the model and the boot proves it of the machine, so the two
/// cannot drift apart silently.
#[test]
fn element_mixed_shape() {
    let mut ast = setup_test("element_mixed/dialect.s");
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
        indexed,
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
        &indexed,
    );
    // Every element's own type, not the first element's and not a width:
    // unsigned elements zero-extend, signed ones sign-extend.
    for expected in ["lbu a0,", "lh a2,", "lwu a4,", "lw a6,"] {
        assert!(
            asm.contains(expected),
            "expected `{expected}` for the element it resolved:\n{asm}"
        );
    }
    bless_asm(
        "element_mixed/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("element_mixed", &asm);
    assert_eq!(
        stdout, "",
        "element_mixed computes and exits cleanly with no output"
    );
}
