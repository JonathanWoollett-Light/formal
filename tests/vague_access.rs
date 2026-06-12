mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// A store whose offset the verifier only knows as a *range* must record its
/// maximal span — `(0..4)..(6..10)` fills `0..10` — because the accessed-ranges
/// serve two purposes that both demand it: they say which bytes an access
/// *could touch* (so nothing that might be read at runtime is ever elided from
/// the generated data), and which bytes' contents are no longer known (an
/// uncertainly-addressed store leaves every byte in its span unknown rather
/// than leaving a stale known value behind).
#[test]
fn vague_offset_records_maximal_span() {
    let system = InnerVerifierConfiguration {
        sections: Default::default(),
        harts: 1,
    };
    let configuration = TypeConfiguration::new();
    let mut state = State::new(&system, &configuration);

    // A 4-byte store whose offset is only known to lie in 0..=6.
    state.record_access(
        &MemoryLabel::Global {
            label: Label::from("x"),
        },
        &MemoryValueU64 { start: 0, stop: 6 },
        4,
    );

    // The recorded range is the whole span 0..10, not any single placement.
    assert_eq!(
        state.accessed,
        vec![(Label::from("x"), BTreeSet::from([(0, 10)]))]
            .into_iter()
            .collect::<AccessedRanges>()
    );
}

/// The codegen side of the same property: a recorded range that only
/// *partially* overlaps a descriptor field keeps the **whole** field (there is
/// no sub-field elision), and every dead byte below the range survives as
/// padding — so an under-determined access can never lose bytes it might
/// touch.
#[test]
fn partially_covered_field_is_emitted_whole() {
    let ast = setup_test("vague_access");

    // Hand-built proof outputs: `x: u8`, and a (vague) access spanning bytes
    // 20..25 of its descriptor — cutting *into* the length field (16..24) and
    // covering the locality byte (24..25).
    let configuration = TypeConfiguration(
        vec![(Label::from("x"), (LabelLocality::Global, Type::U8))]
            .into_iter()
            .collect(),
    );
    let accessed: AccessedRanges = vec![(Label::from("__x_type"), BTreeSet::from([(20, 25)]))]
        .into_iter()
        .collect();

    let asm = emit_executable(ast, &configuration, &accessed);
    let expected = ".global _start
_start:
    #$ x global u8
    la t0, __x_type  # #& t0, x
__halt:
    wfi
    j __halt

.section .data
__x_type:
    .zero 16                # never accessed at runtime (padding)
    .dword 0
    .byte 1

.section .bss
    .balign 8
x:
    .zero 1
";
    assert_eq!(normalize(asm), expected);
}
