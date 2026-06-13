#[path = "../common/mod.rs"]
mod common;

use common::*;
use formal::verifier_types::*;
use formal::*;
use std::collections::BTreeSet;

/// A store whose offset the verifier only knows as a *range* must record its
/// maximal span (`(0..4)..(6..10)` fills `0..10`) because the accessed-ranges
/// serve two purposes that both demand it: they say which bytes an access
/// *could touch* (so nothing that might be read at runtime is ever elided from
/// the generated data), and which bytes' contents are no longer known (an
/// uncertainly-addressed store leaves every byte in its span unknown rather
/// than leaving a stale known value behind).
#[test]
fn vague_offset_records_maximal_span() {
    // A 4-byte store whose offset is only known to lie in 0..=6, recorded into
    // the explorer's accessed-ranges union the way the verifier records it.
    let mut accessed = AccessedRanges::default();
    record_access_into(
        &Default::default(),
        &mut accessed,
        &MemoryLabel::Global {
            label: Label::from("x"),
        },
        &MemoryValueU64 { start: 0, stop: 6 },
        4,
    );

    // The recorded range is the whole span 0..10, not any single placement.
    assert_eq!(
        accessed,
        vec![(Label::from("x"), BTreeSet::from([(0, 10)]))]
            .into_iter()
            .collect::<AccessedRanges>()
    );
}

/// The codegen side of the same property: a recorded range that only
/// *partially* overlaps a descriptor field keeps the **whole** field: there is
/// no sub-field elision (a `.dword` holding a relocation cannot be split), so
/// an under-determined access can never lose bytes it might touch.
#[test]
fn partially_covered_field_is_emitted_whole() {
    let ast = setup_test("vague_access/dialect.s");
    // The Python-like source must translate exactly to the stored dialect (the
    // same pin style as the emitted RISC-V at the other end of the pipeline).
    let translated = hl::translate(include_str!("input.hl")).expect("hl translation failed");
    assert_eq!(normalize(translated), normalize(include_str!("dialect.s")));

    // Hand-built proof outputs: `x: u8`, and a (vague) access spanning bytes
    // 20..25 of its descriptor, cutting *into* the length field (16..24) and
    // covering the locality byte (24..25). A range-shaped access also marks its
    // region uncompactable (the verifier records both together), so the region
    // keeps the padded layout: both touched fields are emitted whole at their
    // original offsets behind `.zero` padding.
    let configuration = TypeConfiguration(
        vec![(Label::from("x"), (LabelLocality::Global, Type::U8))]
            .into_iter()
            .collect(),
    );
    let accessed: AccessedRanges = vec![(Label::from("__x_type"), BTreeSet::from([(20, 25)]))]
        .into_iter()
        .collect();
    let uncompactable = BTreeSet::from([Label::from("__x_type")]);

    let asm = emit_executable(
        ast,
        &configuration,
        &accessed,
        &Default::default(),
        &uncompactable,
        &Default::default(),
    );
    let expected = normalize(include_str!("emitted.s"));
    assert_eq!(normalize(asm), expected);
}
