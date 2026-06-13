#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::*;

/// "Hello World!" on **Linux** (a hosted RISC-V process), the counterpart to
/// the bare-metal `uart_hello`. The source is two lines, `print("Hello
/// World!\n")` and an `exit` syscall; the std library's `print` (prepended by
/// the compiler) measures the string and writes it to stdout with the Linux
/// `write` system call via `ecall`. The whole program is verified, lowered to a
/// **static RISC-V ELF**, and **run under the user-mode `qemu-riscv64`**,
/// asserting it prints `Hello World!`. This pins that `print`, `ecall`, and the
/// syscall registers (`a2`/`a7`) work end to end.
#[test]
fn linux_hello() {
    let mut ast = setup_test("linux_hello/dialect.s");
    // The Python-like source (with the prepended std `print`) translates exactly
    // to the stored dialect.
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // A single hosted hart, no memory-mapped regions: `print` reaches the
    // outside world through `ecall`, not a raw store, so nothing is configured.
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

    // Pin the exact lowered program, then build it into a static ELF and run it.
    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &transitions,
        &uncompactable,
        &pinned_nodes,
    );
    bless_asm(
        "linux_hello/emitted.s",
        asm.clone(),
        include_str!("emitted.s"),
    );

    let stdout = run_linux("linux_hello", &asm);
    assert_eq!(
        stdout, "Hello World!",
        "linux_hello should print \"Hello World!\" to stdout"
    );
}
