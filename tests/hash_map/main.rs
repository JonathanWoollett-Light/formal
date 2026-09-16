#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// A hash map from `std`, proven correct at compile time: a Swiss table
/// (abseil's `raw_hash_set` in its portable byte-wise form) over u32 keys with
/// capacity 16. Twelve keys exercise H1 collisions (nine probe from the same
/// window and one spills to the next), a shared H2 (keys 1 and 2049, rejected
/// by the key compare), an in-place update, and the erase rule's three shapes:
/// a removal that leaves DELETED (probed past by a later find, reused by a
/// reinsert through the cloned control byte), one that leaves EMPTY (past
/// which a find still reaches a later lane of the window), and one whose
/// backward run hits `hm_run`'s cap of 8 through the clones. Six misses, one
/// of them stopping after a single window on an EMPTY lane. Every slot, value,
/// control byte (clones included) and the key count are `require`d. Runs under
/// `qemu-riscv64` and writes `10 5` (the key count and the last removed slot).
#[test]
fn hash_map() {
    let mut ast = setup_test("hash_map/dialect.s");
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
    bless_asm("hash_map/emitted.s", asm.clone(), include_str!("emitted.s"));

    let stdout = run_linux("hash_map", &asm);
    assert_eq!(
        stdout, "10 5",
        "hash_map prints the key count and the last removed slot"
    );
}
