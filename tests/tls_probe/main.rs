#[path = "../common/mod.rs"]
mod common;
use common::*;
use formal::verifier_types::*;
use formal::*;

/// **Per-hart thread-local storage, end to end.** Two harts (`-smp 2`) each claim
/// a rank by atomically fetch-adding a zero-init counter, store a distinct value
/// (`rank + 1`) in a `thread` variable `mine`, read it back, and write it to a
/// per-rank global slot; the last finisher sums the slots (`1 + 2 = 3`) to the
/// UART. The verifier models `mine` as a distinct copy per hart -- this test
/// proves the *codegen* does too: with the old single-copy thread-local codegen
/// (one fixed address for all harts) the two harts would share one `mine`, clobber
/// each other, and the sum would not be `3`. It is the runtime check behind the
/// per-hart TLS lowering (N copies + a `tp = mhartid * block_size` base).
#[test]
fn tls_probe() {
    let mut ast = setup_test("tls_probe/dialect.s");
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
    eprintln!("tls_probe: {} steps", trace.len());
    unsafe {
        remove_untouched(&mut ast, &v.touched);
        remove_branches(&mut ast, &v.jumped);
    }
    let serial = unsafe {
        run_program_smp(
            "tls_probe",
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
    assert_eq!(serial, "3", "per-hart thread-local sum (1+2)");
}
