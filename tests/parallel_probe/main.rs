#[path = "../common/mod.rs"]
mod common;
use common::*;
use formal::verifier_types::*;
use formal::*;

/// **Parallel work-sharing across harts, end to end.** Two harts boot (`-smp 2`)
/// and run the lock-free pattern the parallel fannkuch is built on: each claims a
/// unique rank by atomically fetch-adding a zero-init global counter (`amoadd.w`),
/// does its per-hart work (here a trivial `rank + 1`), writes the result to its
/// own slot, then atomically bumps a `done` counter; the hart that sees `done`
/// reach the last value combines the slots (`1 + 2`) and writes the total to the
/// UART. No start barrier (globals are zero at boot) and no spin (the last
/// finisher is detected by the atomic's return value). The verifier proves this
/// across every 2-hart interleaving; QEMU boots two harts and the UART gets `3`.
#[test]
fn parallel_probe() {
    let mut ast = setup_test("parallel_probe/dialect.s");
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));
    let sections = vec![Section {
        address: MemoryValueI64::from(0x10000000),
        size: MemoryValueI64::from(1),
        permissions: Permissions::Write,
        volatile: true,
    }];
    let explorerer = unsafe {
        Explorerer::new(
            ast,
            &[InnerVerifierConfiguration {
                sections: sections.clone(),
                harts: 2,
            }],
        )
        .expect("construct")
    };
    let (trace, result) = unsafe { trace_valid_path(explorerer) };
    let v = expect_valid(&trace, result);
    eprintln!("parallel_probe: {} steps", trace.len());
    unsafe {
        remove_untouched(&mut ast, &v.touched);
        remove_branches(&mut ast, &v.jumped);
    }
    let serial = unsafe {
        run_program_smp(
            "parallel_probe",
            2,
            false,
            ast,
            &v.configuration,
            &v.accessed,
            &v.transitions,
            &v.uncompactable,
            &v.pinned_nodes,
        )
    };
    assert_eq!(serial, "3", "sum of slots (1+2)");
}
