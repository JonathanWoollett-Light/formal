//! Measures how much of the verifier's exploration would be repeated without
//! the visited set the pointer-free engines keep (`Visited` in src/explore.rs),
//! the numbers behind the state-convergence note in DEVELOPMENT.md §11. Two
//! interleavings that reach the same `Continuation` (state + per-hart fronts +
//! active hart) have identical futures, so exploring both is wasted work. This
//! drives the pooled engine's worklist over a program twice, without and with
//! the set, and reports the steps each took, the distinct states, and whether
//! the six grow-only outputs came out identical, which is the soundness claim
//! for skipping duplicates.
//!
//! Usage: `cargo run --profile test --example converge -- [--uart] <test> <harts>...`
//! (the test profile: optimised, with the verifier's debug assertions kept).
//! `CONVERGE_NOHASH=1` skips hashing on the plain run, to time the visited
//! set's own cost.
use formal::verifier_types::{
    AccessTransitions, AccessedRanges, IndexLowerings, TypeConfiguration,
};
use formal::*;
use std::collections::{BTreeSet, HashMap};
use std::path::PathBuf;
use std::ptr::NonNull;
use std::time::Instant;

fn load(test: &str) -> Option<NonNull<AstNode>> {
    let dir = env!("CARGO_MANIFEST_DIR");
    let path = PathBuf::from(format!("{dir}/tests/{test}/dialect.s"));
    let source = std::fs::read_to_string(&path).expect("read dialect.s");
    let unified = source.replace("\r\n", "\n");
    let source = if cfg!(windows) {
        unified.replace('\n', "\r\n")
    } else {
        unified
    };
    let chars: Vec<char> = source.chars().collect();
    let mut ast = new_ast(&chars, path);
    compress(&mut ast);
    ast
}

/// The oracle's winning configuration, exactly as the tests obtain it.
unsafe fn oracle_configuration(
    ast: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
) -> TypeConfiguration {
    let mut explorer = Explorerer::new(ast, systems).expect("oracle: construction");
    loop {
        match explorer.next_step().expect("oracle: step") {
            ExplorePathResult::Continue(next) => explorer = next,
            ExplorePathResult::Valid(valid) => return valid.configuration,
            ExplorePathResult::Invalid => panic!("oracle: the program is invalid"),
        }
    }
}

struct Outputs {
    touched: BTreeSet<NonNull<AstNode>>,
    jumped: BTreeSet<NonNull<AstNode>>,
    accessed: AccessedRanges,
    transitions: AccessTransitions,
    uncompactable: BTreeSet<Label>,
    pinned_nodes: BTreeSet<NonNull<AstNode>>,
    indexed: IndexLowerings,
}

struct Run {
    steps: u64,
    skipped: u64,
    distinct: u64,
    /// Repeats reached at a different depth from the state's first visit, and
    /// the largest such distance. Zero on every program today: a repeat is a
    /// commuting racy stretch's other order, reached in the same BFS wave,
    /// which is what the wave-window mode in DEVELOPMENT.md §11 rests on.
    far_repeats: u64,
    max_distance: u32,
    max_frontier: usize,
    seconds: f64,
    outputs: Outputs,
}

/// The pooled worklist of `verify_configuration_pooled`, as a stack so the
/// frontier stays small, with a visited set when `dedup`.
unsafe fn explore(
    ast_head: Option<NonNull<AstNode>>,
    systems: &[InnerVerifierConfiguration],
    configuration: &TypeConfiguration,
    dedup: bool,
) -> Run {
    let ast = Ast::index(ast_head);
    let mut outputs = Outputs {
        touched: BTreeSet::new(),
        jumped: BTreeSet::new(),
        accessed: AccessedRanges::new(),
        transitions: AccessTransitions::new(),
        uncompactable: BTreeSet::new(),
        pinned_nodes: BTreeSet::new(),
        indexed: IndexLowerings::new(),
    };
    let mut work: Vec<(u32, Continuation)> = Vec::new();
    for system in systems {
        let mut sinks = RecordSinks {
            accessed: &mut outputs.accessed,
            transitions: &mut outputs.transitions,
            uncompactable: &mut outputs.uncompactable,
            pinned_nodes: &mut outputs.pinned_nodes,
            indexed: &mut outputs.indexed,
        };
        let cont = seed(&ast, system, configuration, &mut sinks)
            .expect("seed")
            .expect("the entry is invalid under the oracle's configuration");
        work.push((0, cont));
    }
    // Digest to the depth first seen at, so a repeat's distance is measured.
    let mut seen: HashMap<[u8; 16], u32> = HashMap::new();
    let (mut steps, mut skipped, mut max_frontier) = (0u64, 0u64, 0usize);
    let (mut far_repeats, mut max_distance) = (0u64, 0u32);
    let started = Instant::now();
    let hash = dedup || std::env::var_os("CONVERGE_NOHASH").is_none();
    while let Some((depth, cont)) = work.pop() {
        if hash {
            let key = digest(&postcard::to_stdvec(&cont).expect("serialise continuation"));
            let fresh = match seen.get(&key) {
                Some(&first) => {
                    let distance = depth.abs_diff(first);
                    far_repeats += u64::from(distance > 0);
                    max_distance = max_distance.max(distance);
                    false
                }
                None => {
                    seen.insert(key, depth);
                    true
                }
            };
            if dedup && !fresh {
                skipped += 1;
                continue;
            }
        }
        steps += 1;
        if steps % 200_000 == 0 {
            eprintln!(
                "  ... {steps} steps, {} distinct, frontier {}, {:.0}s",
                seen.len(),
                work.len(),
                started.elapsed().as_secs_f64()
            );
        }
        let mut sinks = RecordSinks {
            accessed: &mut outputs.accessed,
            transitions: &mut outputs.transitions,
            uncompactable: &mut outputs.uncompactable,
            pinned_nodes: &mut outputs.pinned_nodes,
            indexed: &mut outputs.indexed,
        };
        let outcome = step(
            &cont,
            &ast,
            configuration,
            &mut outputs.touched,
            &mut outputs.jumped,
            &mut sinks,
        )
        .expect("step");
        if let Some(Terminal::Invalid) = outcome.terminal {
            panic!("the program is invalid under the oracle's configuration");
        }
        work.extend(outcome.successors.into_iter().map(|s| (depth + 1, s)));
        max_frontier = max_frontier.max(work.len());
    }
    Run {
        steps,
        skipped,
        distinct: seen.len() as u64,
        far_repeats,
        max_distance,
        max_frontier,
        seconds: started.elapsed().as_secs_f64(),
        outputs,
    }
}

fn main() {
    let mut args = std::env::args().skip(1).peekable();
    // `--uart` seeds the QEMU virt UART the bare-metal probes write to, as
    // their tests do; without it the verifier refuses the store as undescribed.
    let uart = args.peek().is_some_and(|a| a == "--uart");
    if uart {
        args.next();
    }
    let test = args
        .next()
        .expect("usage: converge [--uart] <test> <harts>...");
    let harts: Vec<u8> = args.map(|h| h.parse().expect("hart count")).collect();
    let sections = if uart {
        vec![Section {
            address: formal::verifier_types::MemoryValueI64::from(0x10000000),
            size: formal::verifier_types::MemoryValueI64::from(1),
            permissions: Permissions::Write,
            volatile: true,
        }]
    } else {
        Vec::new()
    };
    let systems: Vec<InnerVerifierConfiguration> = harts
        .iter()
        .map(|&harts| InnerVerifierConfiguration {
            sections: sections.clone(),
            harts,
        })
        .collect();
    let ast = load(&test);
    let configuration = unsafe { oracle_configuration(ast, &systems) };
    eprintln!("{test} harts={harts:?}: oracle configuration found; exploring without dedup");
    let plain = unsafe { explore(ast, &systems, &configuration, false) };
    eprintln!("exploring with dedup");
    let deduped = unsafe { explore(ast, &systems, &configuration, true) };

    let same = plain.outputs.touched == deduped.outputs.touched
        && plain.outputs.jumped == deduped.outputs.jumped
        && plain.outputs.accessed == deduped.outputs.accessed
        && plain.outputs.transitions == deduped.outputs.transitions
        && plain.outputs.uncompactable == deduped.outputs.uncompactable
        && plain.outputs.pinned_nodes == deduped.outputs.pinned_nodes
        && plain.outputs.indexed == deduped.outputs.indexed;
    let saved = 100.0 * (1.0 - deduped.steps as f64 / plain.steps.max(1) as f64);
    println!(
        "{test}\tharts={harts:?}\tsteps={}\tdistinct={}\tdedup_steps={}\tskipped={}\tsaved={saved:.1}%\tplain={:.2}s\tdedup={:.2}s\tfrontier={}/{}\tfar_repeats={}\tmax_repeat_distance={}\toutputs_identical={same}",
        plain.steps,
        plain.distinct,
        deduped.steps,
        deduped.skipped,
        plain.seconds,
        deduped.seconds,
        plain.max_frontier,
        deduped.max_frontier,
        plain.far_repeats,
        plain.max_distance
    );
}
