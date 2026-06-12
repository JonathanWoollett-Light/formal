// The verifier must never abort the process: every failure that was previously a
// `todo!` / `unimplemented!` / `panic!` / `unreachable!` / `unwrap` / `expect` is
// converted into a `CompilerError` returned via `ExplorePathResult::Error`, so callers
// (e.g. tests) get the error *and* the trace instead of a dead test binary. These denies
// enforce that no such throw is reintroduced.
#![deny(
    clippy::unwrap_used,
    clippy::expect_used,
    clippy::panic,
    clippy::todo,
    clippy::unimplemented,
    clippy::unreachable
)]

use crate::ast::*;
use crate::verifier_types::*;
use itertools::Itertools;
use sha2::Digest;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::once;
use std::ops::ControlFlow;
use std::ptr::null_mut;
use std::{collections::VecDeque, ptr::NonNull};
use thiserror::Error;
use tracing::error;
use tracing::info;
use tracing::trace;
use tracing::warn;

/// Replacement for `.unwrap()`/`.expect()` on verifier invariants: converts an
/// `Option`/`Result` into a `Result<_, CompilerError>` carrying a
/// [`CompilerError::Internal`] with the given context when the value is absent.
/// Lets the `?` operator propagate the failure instead of panicking.
trait OrInternal<T> {
    fn internal(self, what: &str) -> Result<T, CompilerError>;
}
impl<T> OrInternal<T> for Option<T> {
    fn internal(self, what: &str) -> Result<T, CompilerError> {
        self.ok_or_else(|| CompilerError::Internal(what.to_string()))
    }
}
impl<T, E: std::fmt::Debug> OrInternal<T> for Result<T, E> {
    fn internal(self, what: &str) -> Result<T, CompilerError> {
        self.map_err(|e| CompilerError::Internal(format!("{what}: {e:?}")))
    }
}

/// The type to explore in order from best to worst.
fn type_list() -> Vec<Type> {
    vec![
        Type::U8,
        Type::I8,
        Type::U16,
        Type::I16,
        Type::U32,
        Type::I32,
        Type::U64,
        Type::I64,
    ]
}

/// Contains the configuration of the system
#[derive(Debug)]
pub struct VerifierConfiguration {
    pub configuration: InnerVerifierConfiguration,
    pub next: *mut VerifierNode,
}
#[derive(Debug, Clone)]
pub struct InnerVerifierConfiguration {
    pub sections: Vec<Section>,
    pub harts: u8,
}

#[derive(Debug, Clone)]
pub struct Section {
    pub address: MemoryValueI64,
    pub size: MemoryValueI64,
    pub permissions: Permissions,
    pub volatile: bool,
}
#[derive(Debug, Clone)]
pub enum Permissions {
    Read,
    Write,
    ReadWrite,
}

#[derive(Debug, Clone, Copy)]
pub enum PrevVerifierNode {
    Root(*mut VerifierConfiguration),
    Branch(*mut VerifierNode),
}
impl PrevVerifierNode {
    fn branch(&self) -> Option<&*mut VerifierNode> {
        match self {
            Self::Branch(branch) => Some(branch),
            Self::Root(_) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd, Eq, Ord)]
pub enum InnerNextVerifierNode {
    Branch(Vec<*mut VerifierNode>),
    Leaf(*mut VerifierLeafNode),
}

/// We use a tree to trace the execution of the program,
/// then when conditions are required it can resolve them
/// by looking back at the trace.
#[derive(Debug)]
pub struct VerifierNode {
    // The previous node in global execution.
    pub prev: PrevVerifierNode,
    pub root: *mut VerifierConfiguration,
    // Current hart.
    pub hart: u8,
    pub node: NonNull<AstNode>,
    pub next: InnerNextVerifierNode,
}

pub enum OuterVerifierNode {
    Leaf(VerifierLeafNode),
    Branch(VerifierNode),
}

// TODO Support some amount of state caching so it doesn't need to re-traverse the whole tree each step to find state.
#[derive(Debug)]
pub struct VerifierLeafNode {
    // The previous node.
    pub prev: *mut VerifierNode,
    // The nodes where variables where first encountered on this path.
    pub variable_encounters: BTreeMap<Label, *mut VerifierNode>,
    // The most recent node for each hart.
    pub hart_fronts: BTreeMap<u8, *mut VerifierNode>,
}

/// Localites in order of best to worst
fn locality_list() -> Vec<Locality> {
    vec![Locality::Thread, Locality::Global]
}

// `wfi` is less racy than instructions like `sw` or `lw` so we could treat it more precisely
// and allow a larger domain of possible programs. But for now, we treat it like `sw` or
// `lw` this means there exist some valid usecases that this will report as invalid, and
// for valid use cases it will be slower as it needs to explore and validate paths it could never
// reach in practice.
pub struct Explorerer {
    #[cfg(debug_assertions)]
    pub hash: sha2::Sha256,
    #[cfg(debug_assertions)]
    pub last_out: Option<TypeConfiguration>,
    #[cfg(debug_assertions)]
    pub counter: usize,
    /// Program configurations that have been found to be invalid.
    #[cfg(debug_assertions)]
    pub excluded: BTreeSet<TypeConfiguration>,
    /// Pointer to the first AST node — verification (and execution) starts from the
    /// first line of the program (there is no explicit `.global`/`_start:` entry).
    pub start_ptr: NonNull<AstNode>,
    /// The different systems configurations to verify.
    pub systems: Vec<*mut VerifierConfiguration>,
    // The current program configuration (e.g. variable types).
    pub configuration: TypeConfiguration,
    // The queue of unexplored leaf nodes.
    pub queue: VecDeque<*mut VerifierLeafNode>,
    // All the nodes that are touched.
    pub touched: BTreeSet<NonNull<AstNode>>,
    // All the branch nodes that jump.
    pub jumped: BTreeSet<NonNull<AstNode>>,
    /// The byte ranges of each memory region the program accesses at **runtime**,
    /// unioned over every replayed path (see [`AccessedRanges`]). Like `touched`,
    /// this only ever grows (entries from since-abandoned configurations remain),
    /// so it over-approximates the final program's accesses — sound for dead-data
    /// elimination, which must never drop a byte any path could read.
    pub accessed: AccessedRanges,
    /// Per-node pointer-arithmetic transitions, unioned over every replayed path
    /// (see [`AccessTransitions`]); drives the instruction rewriting of layout
    /// compaction in codegen. Grows like `accessed`.
    pub transitions: AccessTransitions,
    /// Regions accessed through an under-determined (range) offset: codegen must
    /// keep their padded layout (see [`AccessTransitions`]). Grows like `accessed`.
    pub uncompactable: BTreeSet<Label>,
    /// Nodes that must keep their original immediate (they also executed with a
    /// raw address, scalar operand, or range offset). Grows like `accessed`.
    pub pinned_nodes: BTreeSet<NonNull<AstNode>>,
    // When a variable is 1st encountered in a path it is added here with an iterator over all the
    // possible types, then a type is set in the configuration by calling `.next` on this iterator.
    //
    // When an invalid path is found, all branches are backtraced to the 1st encounter of the most recently
    // encountered variable, then the next type is pulled from the iterator and tested. If `.next`
    // returns `None` then the iterator is removed and all branches are backtraced to the 1st encoutner
    // of the 2nd most recently encountered variable. If the types list is emptied a program with no valid
    // configuration has been found.
    //
    // Variables may be encountered in different orders in different paths e.g.
    // ```
    // if x = 2
    //   y = 1
    // z = 1
    // ```
    // The ordering does not matter, we must simply iterate through exploring combinations
    // and the most recently encountered (in any of the possible paths) is just the easies
    // way that will be naively efficient.
    pub types: BTreeMap<Label, Box<dyn Iterator<Item = (Locality, Type)>>>,
    pub encountered: Vec<Label>,
}

impl Explorerer {
    pub unsafe fn new(
        ast: Option<NonNull<AstNode>>,
        systems: &[InnerVerifierConfiguration],
    ) -> Result<Self, CompilerError> {
        // You cannot verify a program that starts running on 0 harts.
        if !systems.iter().all(|x| x.harts > 0) {
            return Err(CompilerError::Internal(
                "cannot verify a program that starts running on 0 harts".to_string(),
            ));
        }

        // Execution starts from the first line of the program (like Python — there
        // is no explicit `.global`/`_start:` entry; the runnable entry point is added
        // later, by codegen, to the program the verifier emits).
        let start_ptr = ast.internal("new: the AST is empty")?;

        // To avoid retracing paths we record type combinations that have been found to be invalid.
        #[cfg(debug_assertions)]
        let excluded = BTreeSet::new();

        // The different system configurations to explore.
        // When we have 1..=3 harts the initial queue will contain
        // `[(_start, hart 0), (_start, hart 0), (_start, hart 0)]`
        // where each entry has a number of predeccessors e.g. `(_start, hart 1)`
        // up to the number of harts for that path.
        let systems = systems
            .iter()
            .map(|system| {
                Box::into_raw(Box::new(VerifierConfiguration {
                    configuration: system.clone(),
                    next: null_mut(),
                }))
            })
            .collect::<Vec<_>>();

        // info!("systems: {systems:?}");

        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let configuration = TypeConfiguration::new();

        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let touched = BTreeSet::<NonNull<AstNode>>::new();

        // To remove uneeded branches we track the branches that actually jump.
        let jumped = BTreeSet::new();

        // For each system configuration depending on the number of harts we set up an initial node
        // for each hart, the ordering of these initial nodes doesn't matter (as they all point at
        // the first instruction).
        let queue = systems
            .iter()
            .copied()
            .map(|root| build_initial_chain(root, start_ptr, BTreeMap::new()))
            .collect::<Result<VecDeque<_>, CompilerError>>()?;

        // We return the explorer and it's contained state.
        #[cfg(debug_assertions)]
        let x = Self {
            hash: sha2::Sha256::new(),
            last_out: None,
            systems,
            start_ptr,
            excluded,
            configuration,
            touched,
            queue,
            jumped,
            accessed: Default::default(),
            transitions: Default::default(),
            uncompactable: Default::default(),
            pinned_nodes: Default::default(),
            types: Default::default(),
            encountered: Default::default(),
            counter: 0,
        };
        #[cfg(not(debug_assertions))]
        let x = Self {
            systems,
            start_ptr,
            configuration,
            touched,
            queue,
            jumped,
            accessed: Default::default(),
            transitions: Default::default(),
            uncompactable: Default::default(),
            pinned_nodes: Default::default(),
            types: Default::default(),
            encountered: Default::default(),
        };
        Ok(x)
    }

    /// Merges the accessed-ranges, pointer transitions and uncompactable set a
    /// replayed [`State`] recorded into the unions kept across all explored
    /// paths (see [`AccessedRanges`]/[`AccessTransitions`]). Set union is
    /// idempotent, so merging the same replayed prefix repeatedly is harmless.
    fn merge_accessed(&mut self, state: &State) {
        for (label, ranges) in &state.accessed {
            self.accessed
                .entry(label.clone())
                .or_default()
                .extend(ranges.iter().copied());
        }
        for (node, edges) in &state.transitions {
            self.transitions
                .entry(*node)
                .or_default()
                .extend(edges.iter().cloned());
        }
        self.uncompactable
            .extend(state.uncompactable.iter().cloned());
        self.pinned_nodes.extend(state.pinned_nodes.iter().copied());
    }

    // Advance the verifier by one instruction.
    pub unsafe fn next_step(mut self) -> Result<ExplorePathResult, CompilerError> {
        #[cfg(debug_assertions)]
        {
            self.counter += 1;

            if let Some(old) = &mut self.last_out {
                if *old != self.configuration {
                    info!("{}", self.configuration);
                    *old = self.configuration.clone();
                }
            } else {
                info!("{}", self.configuration);
                self.last_out = Some(self.configuration.clone());
            }
        }

        // debug!("excluded: {:?}", self.excluded);
        // debug!("{:?}", self.configuration);
        // The queue represents all the nodes that need to be explored, the ordering of the queue
        // does not matter. When parallelising this the queue would not exist and instead we would
        // dispatch each node as a task.
        trace!(
            "queue: {:?}",
            self.queue
                .iter()
                .filter_map(|ptr| ptr.as_ref())
                .collect::<Vec<_>>()
        );

        // Get the next node to explore.
        let Some(leaf_ptr) = self.queue.front().copied() else {
            return Ok(ExplorePathResult::Valid(ValidPathResult {
                configuration: self.configuration.clone(),
                touched: self.touched.clone(),
                jumped: self.jumped.clone(),
                accessed: self.accessed.clone(),
                transitions: self.transitions.clone(),
                uncompactable: self.uncompactable.clone(),
                pinned_nodes: self.pinned_nodes.clone(),
            }));
        };

        #[cfg(debug_assertions)]
        {
            use base64::prelude::*;
            let leaf = leaf_ptr.as_ref().internal("next_step: null leaf")?;
            let branch = leaf.prev.as_ref().internal("next_step: null leaf prev")?;
            let node = branch.node.as_ref();
            let ast = &node.value;
            self.hash.update(format!("{ast:?}"));
            let out = match self.counter {
                _ => self.counter % 1000 == 0,
            };
            if out {
                let buffer = self.hash.finalize_reset();
                let bytes = buffer.as_slice();
                let string = BASE64_STANDARD.encode(bytes);
                info!("hash {}: {string}", self.counter);
            }
        }

        // Get some data.
        let leaf = leaf_ptr.as_mut().internal("next_step: null leaf")?;
        trace!("leaf: {leaf:?}");
        let branch = leaf.prev.as_ref().internal("next_step: null leaf prev")?;
        let ast = branch.node;
        let hart = branch.hart;

        // debug!("hart: {}/{}", hart + 1, harts);
        // debug!("{:?}", branch.node.as_ref().value);

        // Record all the AST node that are reachable.
        // We can use this for naive dead-code analysisand optimization.
        self.touched.insert(ast);

        // Check the current instruction.
        match &branch.node.as_ref().as_ref().this {
            // Instructions which cannot be invalid and do not affect type exploration.
            Instruction::Unreachable(_)
            | Instruction::Li(_)
            | Instruction::Label(_)
            | Instruction::Addi(_)
            | Instruction::Blt(_)
            | Instruction::Csrr(_)
            | Instruction::Bne(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Wfi(_)
            | Instruction::Beq(_)
            | Instruction::J(_)
            // `#@` cannot itself be invalid; its effect (declaring a section) is
            // applied during state replay in `find_state`.
            | Instruction::Region(_) => {}
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                if !self.load_label(leaf, label, cast, locality, hart) {
                    info!("cannot load label in define {:?}", ast.as_ref());
                    return self.outer_invalid_path();
                }
            }
            Instruction::Lat(Lat { register: _, label }) => {
                if !self.load_label(leaf, label, None, None, hart) {
                    info!("cannot load label in lat {:?}", ast.as_ref());
                    return self.outer_invalid_path();
                }
            }
            Instruction::La(La { register: _, label }) => {
                if !self.load_label(leaf, label, None, None, hart) {
                    info!("cannot load label in la {:?}", ast.as_ref());
                    return self.outer_invalid_path();
                }
            }
            // For any store we need to validate the destination is valid.
            Instruction::Sw(Sw {
                to,
                from: _,
                offset,
            }) => {
                self = match self.check_store(leaf_ptr, branch, to, offset, 4)? {
                    ControlFlow::Continue(x) => x,
                    ControlFlow::Break(outcome) => return Ok(outcome),
                };
            }
            Instruction::Sb(Sb {
                to,
                from: _,
                offset,
            }) => {
                self = match self.check_store(leaf_ptr, branch, to, offset, 1)? {
                    ControlFlow::Continue(x) => x,
                    ControlFlow::Break(outcome) => return Ok(outcome),
                };
            }
            // TODO A lot of the checking loads code is duplicated, reduce this duplication.
            // For any load we need to validate the destination is valid.
            Instruction::Ld(Ld {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 8)? {
                    ControlFlow::Continue(x) => x,
                    ControlFlow::Break(outcome) => return Ok(outcome),
                };
            }
            Instruction::Lw(Lw {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 4)? {
                    ControlFlow::Continue(x) => x,
                    ControlFlow::Break(outcome) => return Ok(outcome),
                };
            }
            Instruction::Lb(Lb {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 1)? {
                    ControlFlow::Continue(x) => x,
                    ControlFlow::Break(outcome) => return Ok(outcome),
                };
            }
            // If any fail is encountered then the path is invalid.
            Instruction::Fail(_) => {
                info!("hit fail {:?}", ast.as_ref());
                return self.outer_invalid_path();
            }
            x => {
                return Err(CompilerError::Unsupported(format!(
                    "instruction not handled in next_step: {x:?}"
                )))
            }
        }
        self.queue_up(leaf_ptr)?;
        // The leaf has to maintain it's position at the front of the queue until we queue up new
        // nodes or we backtrace along an invalid path, when an invalid path is encountered we call
        // `outer_invalid_path` which calls `invalid_path` which will deallocate the leaf and set
        // new leaves (and return and never reach this statement).
        // When we only queue up new leaves, the current leaf remains so we need to pop it off here.
        self.queue.pop_front();

        return Ok(ExplorePathResult::Continue(self));
    }

    /// When an invalid path is encountered we need to backtrack from where we can start exploring a
    /// new path. To do this we iterate across all leaves and de-allocate back up 1st encounter of
    /// the last encountered variable (such that we can then try a new path where this variable has
    /// different type infomation).
    /// 1. Pop most recently encountered variable.
    /// 2. De-allocate all nodes below
    pub unsafe fn outer_invalid_path(
        mut self,
    ) -> Result<ExplorePathResult, CompilerError> {
        // Deallocate nodes up to the 1st occurence of the most recently encountered variable.
        // If there is an invalid path without any variables defined, then there is no possible
        // valid path.
        // If the most recently encountered variable has exhausted all possible types, then move
        // on the the 2nd most recently encountered variable.
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some(recent) = self.encountered.pop() {
            debug_assert!(check.next().is_some());
            // Deallocate the path back to the 1st occurence of the variable `recent`.
            self.invalid_path(&recent)?;

            // Check if there any other possible types for this variable
            let is_empty = {
                let iter = self
                    .types
                    .get(&recent)
                    .internal("outer_invalid_path: missing type iterator")?;
                debug_assert_eq!(
                    iter.size_hint().0,
                    iter.size_hint()
                        .1
                        .internal("outer_invalid_path: unbounded type iterator")?
                );
                iter.size_hint().0 == 0
            };

            // Remove the iterator if there are no other possible types to explore.
            if is_empty {
                self.types.remove(&recent);
                continue;
            }

            // If there are more possible types, push the variables back to encountered.
            self.encountered.push(recent);
            return Ok(ExplorePathResult::Continue(self));
        }
        // Everything is deallocated when `self` is dropped.
        Ok(ExplorePathResult::Invalid)
    }

    pub unsafe fn invalid_path(&mut self, recent: &Label) -> Result<(), CompilerError> {
        // I think we might need to track covered ground so we don't retread it.
        #[cfg(debug_assertions)]
        {
            self.excluded.insert(self.configuration.clone());
            trace!("excluded: {:?}", self.excluded);
        }

        // Remove from current type configuration.
        self.configuration.remove(recent);

        // Split leafs into leafs which have encountered the variable and leafs which haven't.
        // We can leave the leafs which haven't encounterd the variable unchanged while we need to
        // deallocated leafs which have encountered it.
        // Insertion-ordered association from each distinct 1st-encounter node to the
        // intersection of the encounters that follow it across the leaves sharing it.
        //
        // This MUST keep a deterministic order. Keying by the raw `*mut VerifierNode`
        // (e.g. a `BTreeMap<*mut VerifierNode, _>`) would order by allocation address,
        // which varies run-to-run and would make the order in which we re-queue the
        // replacement leaves below — and hence the whole exploration order and total
        // step count — non-deterministic. Iterating `self.queue` (itself in deterministic
        // order) and keeping first-insertion order keeps this deterministic.
        let mut encounters: Vec<(*mut VerifierNode, BTreeMap<Label, *mut VerifierNode>)> =
            Vec::new();
        let mut unchanged = VecDeque::new();
        for leaf in self.queue.iter().copied() {
            // Multiple leafs might have the same 1st encounter, in this case these leafs might
            // encounter different variables later, but for encounters before the shared encounter
            // they will all be the same. Given 2 leafs with encounters [a: 1, b: 3, d: 6] and
            // [a: 1, b: 3, d:5] the new leaf that should exist after their deallocation should have
            // only contain encounters that happened before the shared encounter e.g. [a: 1], we can
            // easily determine this by the using the intersection of all encounters (retain where
            // they have the same variable encountered at the same place).
            let mut map = leaf
                .as_ref()
                .internal("invalid_path: null leaf")?
                .variable_encounters
                .clone();
            if let Some(encounter) = map.remove(&recent) {
                if let Some(entry) = encounters.iter_mut().find(|(node, _)| *node == encounter) {
                    entry.1.retain(|k, v| map.get(k) == Some(v));
                } else {
                    encounters.push((encounter, map));
                }
            } else {
                unchanged.push_back(leaf);
            }
        }

        // Set the queue to the leafs which haven't encountered the variable.
        // We will append new leafs later in this scope as leafs to replace the leafs we deallocate.
        self.queue = unchanged;

        // Iterate across leafs we need to deallocate.
        let start_ptr = self.start_ptr;
        for (encounter_ptr, variable_encounters) in encounters {
            let encounter_ref = encounter_ptr
                .as_ref()
                .internal("invalid_path: null encounter node")?;
            let root = encounter_ref.root;
            // If the variable was first encountered at the very first instruction, its
            // encounter node is part of the initial chain (all harts still at the
            // start), so there is no preceding per-hart structure to walk back through —
            // the replacement is a fresh initial chain. Otherwise re-attach a leaf after
            // the encounter's predecessor node.
            let current_opt = if encounter_ref.node == start_ptr {
                None
            } else {
                encounter_ref.prev.branch().copied()
            };
            let harts = root.as_ref().internal("invalid_path: null root")?.configuration.harts;

            // De-allocate the 1st encounter for this variable and its subtree.
            let mut stack = vec![encounter_ptr];
            while let Some(next) = stack.pop() {
                match &next.as_ref().internal("invalid_path: null node")?.next {
                    InnerNextVerifierNode::Branch(branches) => stack.extend(branches),
                    InnerNextVerifierNode::Leaf(leaf) => {
                        dealloc(leaf.cast(), Layout::new::<VerifierLeafNode>())
                    }
                }
                // `next` is a `VerifierNode` (not a leaf) — free it with its own layout.
                dealloc(next.cast(), Layout::new::<VerifierNode>());
            }

            let new_leaf = match current_opt {
                // Re-attach a fresh leaf after the encounter's predecessor node.
                Some(current) => {
                    // Recompute the hart fronts by walking back until every hart is seen.
                    let mut prev = current;
                    let mut hart_fronts = BTreeMap::new();
                    loop {
                        let branch_ref = prev.as_ref().internal("invalid_path: null node")?;
                        hart_fronts.entry(branch_ref.hart).or_insert(prev);
                        if hart_fronts.len() == harts as usize {
                            break;
                        }
                        prev = *branch_ref
                            .prev
                            .branch()
                            .internal("invalid_path: node follows root before all harts seen")?;
                    }
                    let new_leaf = Box::into_raw(Box::new(VerifierLeafNode {
                        prev: current,
                        variable_encounters,
                        hart_fronts,
                    }));
                    current
                        .as_mut()
                        .internal("invalid_path: null current node")?
                        .next = InnerNextVerifierNode::Leaf(new_leaf);
                    new_leaf
                }
                // The encounter was the very first instruction — rebuild the initial
                // chain from the root.
                None => build_initial_chain(root, start_ptr, variable_encounters)?,
            };
            self.queue.push_back(new_leaf);
        }
        Ok(())
    }

    /// Attempts to modify initial types to include a new variable, if it cannot add it,
    /// existing is added to excluded, then returns true.
    ///
    /// # Returns
    ///
    /// - `true` the path is valid.
    /// - `false` the path is invalid.
    fn load_label(
        &mut self,
        leaf: &mut VerifierLeafNode,
        label: &Label,
        ttype: impl Borrow<Option<Type>>, // The type to use for the variable if `Some(_)`.
        locality: impl Borrow<Option<Locality>>, // The locality to use for the variable if `Some(_)`.
        hart: u8,
    ) -> bool {
        // If this is the first encounter of this variable along this path, set it.
        //
        // The variable can be defined in another path, but not yet encountered in this path
        // (another path in another hart or another path in another system configuration).
        leaf.variable_encounters
            .entry(label.clone())
            .or_insert(leaf.prev);

        // If the variable is already defined, the type and locality previously defined must match any given here.
        // E.g.
        // ```
        // define x local u8
        // define x local u8
        // ```
        // is valid, but
        // ```
        // define x local u8
        // define x local u16
        // ```
        // isn't.
        if let Some((existing_locality, existing_type)) = self.configuration.get(label) {
            if let Some(given_type) = ttype.borrow() {
                if given_type != existing_type {
                    return false;
                }
            }
            if let Some(given_locality) = locality.borrow() {
                if given_locality != existing_locality {
                    return false;
                }
            }
            // A thread-local has one copy per hart that touches it: a re-encounter
            // (possibly on a *different* hart) must record that this hart needs a
            // copy too — `State::new` seeds one `.bss` entry per recorded hart, and
            // without this a second hart's access would find no memory behind its
            // `MemoryLabel::Thread { hart }` and die with an internal error.
            if *existing_locality == Locality::Thread {
                let existing_type = existing_type.clone();
                self.configuration
                    .insert(label.clone(), hart, (Locality::Thread, existing_type));
            }
            return true;
        }

        // Get the iterator yielding types for `label` or if this is the 1st encounter adds the new
        // iterator for types.
        // At this point this is the first encounter of the variable in the overall configuration,
        // (since `self.configuration.get(label)` is `None`) but it may have been the case a
        // previous configuration found this variable, set the iterator, encountered an invalid path
        // then backtracked with the iterator advanced to the next type to check.
        // So here we are essentially setting the type of this variable for all paths (across system
        // configurations).
        let iter = self.types.entry(label.clone()).or_insert_with(|| {
            debug_assert!(self.encountered.iter().find(|l| *l == label).is_none());
            self.encountered.push(label.clone());
            let mut localities = locality_list();
            if let Some(given_locality) = locality.borrow() {
                localities.push(*given_locality);
            }
            let mut types = type_list();
            if let Some(given_type) = ttype.borrow() {
                types.push(given_type.clone());
            }
            Box::new(localities.into_iter().cartesian_product(types))
        });

        // Iterate through remaining types to explore until finding a type that doesn't conflict
        // with the specified locality and type.
        //
        // This looks how it does since the example code is valid (assuming x is known at
        // compile-time) and it needs to support this:
        // ```
        // if typeof x = u8
        //   define y _ u8
        // if typeof x = i8
        //   define y _ i8
        // ```
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while let Some((possible_locality, possible_type)) = iter.next() {
            debug_assert!(check.next().is_some());
            // Check the possible type doesn't disagree with the define statement.
            if let Some(given_locality) = locality.borrow() {
                if possible_locality != *given_locality {
                    continue;
                }
            }
            if let Some(given_type) = ttype.borrow() {
                if possible_type != *given_type {
                    continue;
                }
            }

            // You might initially think that we don't need to check this since you assume the
            // iterators gurantee unique new types for variables. But I don't think this is the
            // case, I can't quite fully verbalize it, so I've added this check to test for the
            // case.
            // TODO Check if this can be removed.
            #[cfg(debug_assertions)]
            {
                let mut config = self.configuration.clone();
                config.insert(
                    label.clone(),
                    hart,
                    (possible_locality, possible_type.clone()),
                );
                if self.excluded.contains(&config) {
                    warn!("Encountered a type that has already been excluded");
                    continue;
                }
            }

            // Found valid typing.
            self.configuration
                .insert(label.clone(), hart, (possible_locality, possible_type));
            return true;
        }
        return false;
    }

    unsafe fn check_store(
        mut self,
        leaf_ptr: *mut VerifierLeafNode,
        branch: impl Borrow<VerifierNode>,
        to: impl Borrow<Register>,
        offset: impl Borrow<crate::ast::Offset>,
        type_size: u64,
    ) -> Result<ControlFlow<ExplorePathResult, Self>, CompilerError> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration)?;
        self.merge_accessed(&state);

        // Check the destination is valid.
        match state.registers[branch.borrow().hart as usize].get(to) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) = state
                    .configuration
                    .get(<&Label>::from(from_label))
                    .internal("store: label missing from configuration")?;
                // If attempting to access outside the memory space for the label.
                let full_offset = MemoryValueU64::from(type_size)
                    .add(from_offset)
                    .internal("store: offset overflow")?
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.borrow().value.value)
                            .internal("store: negative offset")?,
                    ))
                    .internal("store: offset overflow")?;
                let size = size(ttype);

                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
                        info!("reached invalid store in path due to attempting to accress memory space past a label, size: {size:?}, offset: {full_offset:?}, node: {:?}", branch.borrow().node.as_ref().value);
                        Ok(ControlFlow::Break(self.outer_invalid_path()?))
                    }
                    true => {
                        // Else we found the label and we can validate that the loading
                        // of a word with the given offset is within the address space.
                        // So we continue exploration.
                        //
                        // Record this store's own bytes directly: `find_state` replays
                        // exclude the instruction being processed, so a store whose
                        // successors all halt (`#?`) would otherwise never enter
                        // `accessed` — and dead-data elimination would elide bytes the
                        // emitted program still writes at runtime.
                        let start_offset = from_offset
                            .clone()
                            .add(&MemoryValueU64::from(
                                u64::try_from(offset.borrow().value.value)
                                    .internal("store: negative offset")?,
                            ))
                            .internal("store: offset overflow")?;
                        record_access_into(
                            &state.descriptor_labels,
                            &mut self.accessed,
                            from_label,
                            &start_offset,
                            type_size,
                        );
                        record_transition_into(
                            &state.descriptor_labels,
                            &mut self.transitions,
                            &mut self.uncompactable,
                            &mut self.pinned_nodes,
                            branch.borrow().node,
                            from_label,
                            from_offset,
                            &start_offset,
                        );
                        Ok(ControlFlow::Continue(self))
                    }
                }
            }
            // For acceses to main memory, we need to validate this is in `sections`.
            Some(MemoryValue::I64(x)) => {
                let start = x
                    .add(&MemoryValueI64::from(offset.borrow().value.value))
                    .internal("store: address overflow")?;
                // Validate against the replayed state's sections: they start as the
                // system-configured ones and grow as the path executes `#@` region
                // declarations.
                let sections = &state.memory.sections;

                // Find a section that the store would be within.
                let mut section_opt = None;
                for s in sections {
                    let required_size = start
                        .sub(&s.address)
                        .internal("store: section offset underflow")?
                        .add(&MemoryValueI64::from(
                            i64::try_from(type_size).internal("store: type size overflow")?,
                        ))
                        .internal("store: section size overflow")?;
                    // Within iff the access starts at/after the section and the bytes
                    // it needs (`required_size`) do not exceed the section's size.
                    let within = match (start.compare(&s.address), required_size.compare(&s.size)) {
                        (
                            RangeOrdering::Greater | RangeOrdering::Equal | RangeOrdering::Matches,
                            RangeOrdering::Less | RangeOrdering::Equal | RangeOrdering::Matches,
                        ) => true,
                        (RangeOrdering::Less | RangeOrdering::Cover, _) => false,
                        (_, RangeOrdering::Greater | RangeOrdering::Cover) => false,
                        pair => {
                            return Err(CompilerError::Unsupported(format!(
                                "store: indeterminate section comparison {pair:?}"
                            )))
                        }
                    };
                    if within {
                        section_opt = Some(s);
                        break;
                    }
                }

                // Check this section supports writing.
                if let Some(section) = section_opt {
                    match section.permissions {
                        Permissions::ReadWrite | Permissions::Write => {
                            // Raw execution of this node: it must keep its
                            // original immediate even if another execution is a
                            // pointer access into a compacted region. (Replays
                            // exclude the checked instruction, so a terminal raw
                            // access pins here or never.)
                            self.pinned_nodes.insert(branch.borrow().node);
                            Ok(ControlFlow::Continue(self))
                        }
                        Permissions::Read => {
                            info!("reached invalid path due to attempt to write to read-only");
                            Ok(ControlFlow::Break(self.outer_invalid_path()?))
                        }
                    }
                } else {
                    info!("reached invalid path due to attempt to write to undescribed memory");
                    Ok(ControlFlow::Break(self.outer_invalid_path()?))
                }
            }
            x => Err(CompilerError::Unsupported(format!("store to {x:?}"))),
        }
    }

    /// Verifies a load is valid for a given configuration.
    unsafe fn check_load(
        mut self,
        leaf_ptr: *mut VerifierLeafNode,
        branch: impl Borrow<VerifierNode>,
        from: impl Borrow<Register>,
        offset: impl Borrow<crate::ast::Offset>,
        type_size: u64,
    ) -> Result<ControlFlow<ExplorePathResult, Self>, CompilerError> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration)?;
        self.merge_accessed(&state);

        // Check the destination is valid.
        match state.registers[branch.borrow().hart as usize].get(from) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) = state
                    .configuration
                    .get(<&Label>::from(from_label))
                    .internal("load: label missing from configuration")?;

                // If attempting to access outside the memory space for the label.
                let offset_value = offset.borrow().value.value;
                let full_offset = MemoryValueU64::from(type_size)
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset_value).internal("load: negative offset")?,
                    ))
                    .internal("load: offset overflow")?
                    .add(from_offset)
                    .internal("load: offset overflow")?;
                let size = size(ttype);
                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
                        info!("reached invalid load in path due to attempting to accress memory space past a label, size: {size:?}, offset: {full_offset:?} ({type_size:?} + {offset_value} + {from_offset:?}), node: {:?}", branch.borrow().node.as_ref().value);
                        Ok(ControlFlow::Break(self.outer_invalid_path()?))
                    }
                    true => {
                        // Else, we found the label and we can validate that the loading
                        // of a word with the given offset is within the address space.
                        // So we continue exploration.
                        //
                        // Record this load's own bytes directly: `find_state` replays
                        // exclude the instruction being processed, so a load whose
                        // successors all halt (`#?`) would otherwise never enter
                        // `accessed` — and dead-data elimination would elide bytes the
                        // emitted program still reads at runtime.
                        let start_offset = from_offset
                            .clone()
                            .add(&MemoryValueU64::from(
                                u64::try_from(offset_value).internal("load: negative offset")?,
                            ))
                            .internal("load: offset overflow")?;
                        record_access_into(
                            &state.descriptor_labels,
                            &mut self.accessed,
                            from_label,
                            &start_offset,
                            type_size,
                        );
                        record_transition_into(
                            &state.descriptor_labels,
                            &mut self.transitions,
                            &mut self.uncompactable,
                            &mut self.pinned_nodes,
                            branch.borrow().node,
                            from_label,
                            from_offset,
                            &start_offset,
                        );
                        Ok(ControlFlow::Continue(self))
                    }
                }
            }
            // For accesses to main memory (raw addresses), every access must be
            // verifiable as safe: the load must fall within a described section —
            // one from the system configuration or one declared by `#@`.
            Some(MemoryValue::I64(x)) => {
                let start = x
                    .add(&MemoryValueI64::from(offset.borrow().value.value))
                    .internal("load: address overflow")?;
                let sections = &state.memory.sections;

                // Find a section that the load would be within.
                let mut section_opt = None;
                for s in sections {
                    let required_size = start
                        .sub(&s.address)
                        .internal("load: section offset underflow")?
                        .add(&MemoryValueI64::from(
                            i64::try_from(type_size).internal("load: type size overflow")?,
                        ))
                        .internal("load: section size overflow")?;
                    // Within iff the load starts at/after the section and the bytes
                    // it needs (`required_size`) do not exceed the section's size.
                    let within = match (start.compare(&s.address), required_size.compare(&s.size)) {
                        (
                            RangeOrdering::Greater | RangeOrdering::Equal | RangeOrdering::Matches,
                            RangeOrdering::Less | RangeOrdering::Equal | RangeOrdering::Matches,
                        ) => true,
                        (RangeOrdering::Less | RangeOrdering::Cover, _) => false,
                        (_, RangeOrdering::Greater | RangeOrdering::Cover) => false,
                        pair => {
                            return Err(CompilerError::Unsupported(format!(
                                "load: indeterminate section comparison {pair:?}"
                            )))
                        }
                    };
                    if within {
                        section_opt = Some(s);
                        break;
                    }
                }

                // Check this section supports reading.
                if let Some(section) = section_opt {
                    match section.permissions {
                        Permissions::ReadWrite | Permissions::Read => {
                            // Raw execution pins the node (see the store arm).
                            self.pinned_nodes.insert(branch.borrow().node);
                            Ok(ControlFlow::Continue(self))
                        }
                        Permissions::Write => {
                            info!("reached invalid path due to attempt to read write-only memory");
                            Ok(ControlFlow::Break(self.outer_invalid_path()?))
                        }
                    }
                } else {
                    info!("reached invalid path due to attempt to read undescribed memory");
                    Ok(ControlFlow::Break(self.outer_invalid_path()?))
                }
            }
            x => Err(CompilerError::Unsupported(format!("load from {x:?}"))),
        }
    }

    /// Queues up the next node to evaluate.
    ///
    /// We look at the next node for the 1st hart and queue this up if its not racy,
    /// if its racy, we look at the 2nd hart and queue it up if its not racy,
    /// if its racy we look at the 3rd hart etc. If all next nodes are racy, we queue
    /// up all racy instructions (since we need to evaluate all the possible ordering of them).
    unsafe fn queue_up(
        &mut self,
        leaf_ptr: *mut VerifierLeafNode,
    ) -> Result<(), CompilerError> {
        // TOOD We duplicate so much work doing `find_state` in a bunch of places and
        // multiple times when the state hasn't change, we should avoid doing this call
        // here (and remove it in other places too).
        let state = find_state(leaf_ptr, &self.configuration)?;
        self.merge_accessed(&state);
        let queue = &mut self.queue;
        let jumped = &mut self.jumped;
        let leaf = leaf_ptr.as_mut().internal("queue_up: null leaf")?;

        // Search the verifier tree for the fronts of all harts.
        let mut fronts = BTreeMap::new();
        let mut current = leaf.prev.as_ref().internal("queue_up: null leaf prev")?;
        let harts = current.root.as_ref().internal("queue_up: null root")?.configuration.harts;
        fronts.insert(current.hart, current.node);
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while fronts.len() < harts as usize {
            debug_assert!(check.next().is_some());
            let PrevVerifierNode::Branch(branch) = current.prev else {
                return Err(CompilerError::Internal(
                    "queue_up: hart front search reached root before all harts found".to_string(),
                ));
            };
            current = branch.as_ref().internal("queue_up: null branch")?;
            fronts.entry(current.hart).or_insert(current.node);
        }

        // debug!(
        //     "fronts: {:?}",
        //     fronts
        //         .iter()
        //         .map(|(hart, ast)| (hart, ast.as_ref().as_ref().this.to_string()))
        //         .collect::<BTreeMap<_, _>>()
        // );

        type Followup = Option<Result<(u8, NonNull<AstNode>), (u8, NonNull<AstNode>)>>;
        let followup = |node: NonNull<AstNode>,
                        hart: u8|
         -> Result<Followup, CompilerError> {
            let instruction = &node.as_ref().as_ref().this;
            Ok(match instruction {
                // Non-racy.
                Instruction::Label(_)
                | Instruction::La(_)
                | Instruction::Lat(_)
                | Instruction::Li(_)
                | Instruction::Addi(_)
                | Instruction::Csrr(_)
                | Instruction::Define(_)
                | Instruction::Blt(_)
                | Instruction::Bne(_)
                | Instruction::Bnez(_)
                | Instruction::Beqz(_)
                | Instruction::Bge(_)
                | Instruction::Fail(_)
                | Instruction::Beq(_)
                | Instruction::J(_) => Some(Err((hart, node))),
                // `#@` is racy: a region only becomes accessible once its declaration
                // executes, so its order relative to other harts' raw accesses is
                // observable — collapsing it would skip the (invalid) interleavings
                // where another hart's access precedes the declaration it needs.
                Instruction::Region(_) => Some(Ok((hart, node))),
                // Possibly racy.
                // If the label is thread local its not racy.
                Instruction::Sb(Sb { to: register, .. })
                | Instruction::Sw(Sw { to: register, .. })
                | Instruction::Ld(Ld { from: register, .. })
                | Instruction::Lw(Lw { from: register, .. })
                | Instruction::Lb(Lb { from: register, .. }) => {
                    let value = state.registers[hart as usize]
                        .get(register)
                        .internal("queue_up: racy access register has no value")?;
                    match value {
                        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr { tag, offset: _ }))) => {
                            match tag {
                                // Racy
                                MemoryLabel::Global { label: _ } => Some(Ok((hart, node))),
                                // Non-racy
                                MemoryLabel::Thread {
                                    label: _,
                                    hart: thart,
                                } => {
                                    assert_eq!(*thart, hart);
                                    Some(Err((hart, node)))
                                }
                            }
                        }
                        // The assumption here is that this hardcoded memory refers to RAM and does
                        // not overlap the `.bss` or `.data` section (this will be checked in
                        // `check_load`) given this assumption it's racy.
                        MemoryValue::I64(_) => Some(Ok((hart, node))),
                        // TODO We hit this in `three.s` we should not hit this, the `from` should
                        // always be `MemoryValue::Ptr`.
                        _ => {
                            return Err(CompilerError::Unsupported(format!(
                                "queue_up followup for {instruction:?} with value {value:?}"
                            )))
                        }
                    }
                }
                // See note on `wfi`.
                Instruction::Wfi(_) => Some(Ok((hart, node))),
                Instruction::Unreachable(_) => None,
                x => {
                    return Err(CompilerError::Unsupported(format!(
                        "queue_up followup: {x:?}"
                    )))
                }
            })
        };

        // The lowest hart non-racy node is enqueued.
        // (or possibly multiples nodes in the case of a conditional jump where
        // we cannot deteremine the condition).

        let classified = fronts
            .iter()
            // TODO Document why reverse order is important here.
            .rev()
            .map(|(&hart, &node)| -> Result<Followup, CompilerError> {
                let node_ref = node.as_ref();
                Ok(match &node_ref.as_ref().this {
                    // Conditional.
                    Instruction::Blt(Blt { rhs, lhs, label }) => {
                        let lhs = state.registers[hart as usize]
                            .get(lhs)
                            .internal("queue_up: blt lhs register has no value")?;
                        let rhs = state.registers[hart as usize]
                            .get(rhs)
                            .internal("queue_up: blt rhs register has no value")?;
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Less) => {
                                jumped.insert(node);
                                let label_node = find_label(node, label)
                                    .internal("queue_up: blt target not found")?;
                                followup(label_node, hart)?
                            }
                            Some(RangeOrdering::Greater | RangeOrdering::Equal) => followup(
                                node_ref.next.internal("queue_up: blt has no next")?,
                                hart,
                            )?,
                            _ => {
                                return Err(CompilerError::Unsupported(
                                    "queue_up: indeterminate blt comparison".to_string(),
                                ))
                            }
                        }
                    }
                    Instruction::Beq(Beq { rhs, lhs, out }) => {
                        let lhs = state.registers[hart as usize]
                            .get(lhs)
                            .internal("queue_up: beq lhs register has no value")?;
                        let rhs = state.registers[hart as usize]
                            .get(rhs)
                            .internal("queue_up: beq rhs register has no value")?;
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Equal) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out)
                                    .internal("queue_up: beq target not found")?;
                                followup(label_node, hart)?
                            }
                            Some(RangeOrdering::Greater | RangeOrdering::Less) => followup(
                                node_ref.next.internal("queue_up: beq has no next")?,
                                hart,
                            )?,
                            _ => {
                                return Err(CompilerError::Unsupported(
                                    "queue_up: indeterminate beq comparison".to_string(),
                                ))
                            }
                        }
                    }
                    Instruction::Bne(Bne { rhs, lhs, out }) => {
                        let lhs = state.registers[hart as usize]
                            .get(lhs)
                            .internal("queue_up: bne lhs register has no value")?;
                        let rhs = state.registers[hart as usize]
                            .get(rhs)
                            .internal("queue_up: bne rhs register has no value")?;
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Greater | RangeOrdering::Less) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out)
                                    .internal("queue_up: bne target not found")?;
                                trace!("bne jumped: {:?}", label_node.as_ref().value);
                                followup(label_node, hart)?
                            }
                            Some(RangeOrdering::Equal) => {
                                trace!("bne no jump");
                                followup(node_ref.next.internal("queue_up: bne has no next")?, hart)?
                            }
                            _ => {
                                return Err(CompilerError::Unsupported(
                                    "queue_up: indeterminate bne comparison".to_string(),
                                ))
                            }
                        }
                    }
                    Instruction::Bnez(Bnez { src, dest }) => {
                        let src = state.registers[hart as usize]
                            .get(src)
                            .internal("queue_up: bnez register has no value")?;

                        // In the case the path is determinate, we either queue up the label
                        // or the next ast node and don't need to actually visit/evaluate
                        // the branch at runtime.
                        match src {
                            MemoryValue::I8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        followup(
                                            node_ref.next.internal("queue_up: bnez has no next")?,
                                            hart,
                                        )?
                                    } else {
                                        return Err(CompilerError::Unsupported(
                                            "queue_up: indeterminate bnez (i8)".to_string(),
                                        ));
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest)
                                        .internal("queue_up: bnez target not found")?;
                                    followup(label_node, hart)?
                                }
                            },
                            MemoryValue::U8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        followup(
                                            node_ref.next.internal("queue_up: bnez has no next")?,
                                            hart,
                                        )?
                                    } else {
                                        return Err(CompilerError::Unsupported(
                                            "queue_up: indeterminate bnez (u8)".to_string(),
                                        ));
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest)
                                        .internal("queue_up: bnez target not found")?;
                                    followup(label_node, hart)?
                                }
                            },
                            MemoryValue::Csr(CsrValue::Mhartid) => {
                                if hart == 0 {
                                    followup(
                                        node_ref.next.internal("queue_up: bnez has no next")?,
                                        hart,
                                    )?
                                } else {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest)
                                        .internal("queue_up: bnez target not found")?;
                                    followup(label_node, hart)?
                                }
                            }
                            x => {
                                return Err(CompilerError::Unsupported(format!(
                                    "queue_up: bnez on {x:?}"
                                )))
                            }
                        }
                    }
                    Instruction::Beqz(Beqz { register, label }) => {
                        let src = state.registers[hart as usize]
                            .get(register)
                            .internal("queue_up: beqz register has no value")?;

                        // In the case the path is determinate, we either queue up the label
                        // or the next ast node and don't need to actually visit/evaluate
                        // the branch at runtime.
                        match src {
                            MemoryValue::U8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        jumped.insert(node);
                                        let label_node = find_label(node, label)
                                            .internal("queue_up: beqz target not found")?;
                                        followup(label_node, hart)?
                                    } else {
                                        return Err(CompilerError::Unsupported(
                                            "queue_up: indeterminate beqz (u8)".to_string(),
                                        ));
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => followup(
                                    node_ref.next.internal("queue_up: beqz has no next")?,
                                    hart,
                                )?,
                            },
                            MemoryValue::I8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        jumped.insert(node);
                                        let label_node = find_label(node, label)
                                            .internal("queue_up: beqz target not found")?;
                                        followup(label_node, hart)?
                                    } else {
                                        return Err(CompilerError::Unsupported(
                                            "queue_up: indeterminate beqz (i8)".to_string(),
                                        ));
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => followup(
                                    node_ref.next.internal("queue_up: beqz has no next")?,
                                    hart,
                                )?,
                            },
                            MemoryValue::Csr(CsrValue::Mhartid) => {
                                if hart == 0 {
                                    jumped.insert(node);
                                    let label_node = find_label(node, label)
                                        .internal("queue_up: beqz target not found")?;
                                    followup(label_node, hart)?
                                } else {
                                    followup(
                                        node_ref.next.internal("queue_up: beqz has no next")?,
                                        hart,
                                    )?
                                }
                            }
                            x => {
                                return Err(CompilerError::Unsupported(format!(
                                    "queue_up: beqz on {x:?}"
                                )))
                            }
                        }
                    }
                    Instruction::Bge(Bge { lhs, rhs, out }) => {
                        let lhs = state.registers[hart as usize]
                            .get(lhs)
                            .internal("queue_up: bge lhs register has no value")?;
                        let rhs = state.registers[hart as usize]
                            .get(rhs)
                            .internal("queue_up: bge rhs register has no value")?;
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Greater | RangeOrdering::Equal) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out)
                                    .internal("queue_up: bge target not found")?;
                                followup(label_node, hart)?
                            }
                            Some(RangeOrdering::Less) => {
                                followup(node_ref.next.internal("queue_up: bge has no next")?, hart)?
                            }
                            _ => {
                                return Err(CompilerError::Unsupported(
                                    "queue_up: indeterminate bge comparison".to_string(),
                                ))
                            }
                        }
                    }
                    Instruction::J(J { dest }) => {
                        jumped.insert(node);
                        let label_node =
                            find_label(node, dest).internal("queue_up: j target not found")?;
                        followup(label_node, hart)?
                    }
                    // Non-conditional
                    Instruction::Label(_)
                    | Instruction::La(_)
                    | Instruction::Lat(_)
                    | Instruction::Li(_)
                    | Instruction::Addi(_)
                    | Instruction::Csrr(_)
                    | Instruction::Define(_)
                    | Instruction::Sw(_)
                    | Instruction::Sb(_)
                    | Instruction::Ld(_)
                    | Instruction::Lw(_)
                    | Instruction::Lb(_)
                    | Instruction::Fail(_)
                    | Instruction::Region(_) => {
                        followup(node_ref.next.internal("queue_up: instruction has no next")?, hart)?
                    }
                    // See note on `wfi`.
                    Instruction::Wfi(_) => {
                        Some(Ok((hart, node_ref.next.internal("queue_up: wfi has no next")?)))
                    }
                    // Blocking.
                    Instruction::Unreachable(_) => None,
                    x => {
                        return Err(CompilerError::Unsupported(format!(
                            "queue_up classify: {x:?}"
                        )))
                    }
                })
            })
            .collect::<Result<Vec<Followup>, CompilerError>>()?;
        let next_nodes: Result<Vec<_>, _> = classified.into_iter().flatten().collect();

        // debug!("racy: {}", next_nodes.is_ok());

        // debug!(
        //     "next: {:?}",
        //     next_nodes
        //         .as_ref()
        //         .map(|racy| racy
        //             .iter()
        //             .map(|(h, n)| format!(
        //                 "{{ hart: {h}, instruction: {} }}",
        //                 n.as_ref().as_ref().this.to_string()
        //             ))
        //             .collect::<Vec<_>>())
        //         .map_err(|(h, n)| format!(
        //             "{{ hart: {h}, instruction: {} }}",
        //             n.as_ref().as_ref().this.to_string()
        //         ))
        // );

        // TODO Currently these does breadth first search by pushing to the back of the queue. It would be more
        // efficient to do depth first search (since this is more likely to hit invalid paths earlier). I remember
        // there was a reason this needed to push to back and be breadth first (but can't remember specifics), try
        // making this depth first.
        match next_nodes {
            // If there was a non-racy node, enqueue this single node.
            Err((hart, non_racy_next)) => {
                let branch_ptr = leaf.prev;
                let branch = branch_ptr.as_mut().internal("queue_up: null branch node")?;
                let new_branch = Box::into_raw(Box::new(VerifierNode {
                    prev: PrevVerifierNode::Branch(branch_ptr),
                    root: branch.root,
                    hart,
                    node: non_racy_next,
                    next: InnerNextVerifierNode::Leaf(leaf_ptr),
                }));
                leaf.prev = new_branch;
                branch.next = InnerNextVerifierNode::Branch(vec![new_branch]);

                queue.push_back(leaf_ptr);
            }
            // If all nodes where racy, enqueue these nodes.
            Ok(racy_nodes) => {
                trace!(
                    "racy_nodes: {:?}",
                    racy_nodes
                        .iter()
                        .map(|(hart, node)| (hart, node.as_ref().value.clone()))
                        .collect::<Vec<_>>()
                );

                let branch_ptr = leaf.prev;
                let branch = branch_ptr.as_mut().internal("queue_up: null branch node")?;
                trace!("racy node branch: {:?}", branch.node.as_ref().value);

                let (new_branches, new_leaves) = racy_nodes
                    .iter()
                    .copied()
                    .map(|(hart, node)| {
                        trace!("racy node new node: {:?}", node.as_ref().value);
                        let new_branch = Box::into_raw(Box::new(VerifierNode {
                            prev: PrevVerifierNode::Branch(branch_ptr),
                            root: branch.root,
                            hart,
                            node,
                            next: InnerNextVerifierNode::Leaf(null_mut()),
                        }));
                        let mut hart_fronts = leaf.hart_fronts.clone();
                        hart_fronts.insert(hart, new_branch);
                        let new_leaf = Box::into_raw(Box::new(VerifierLeafNode {
                            prev: new_branch,
                            variable_encounters: leaf.variable_encounters.clone(),
                            hart_fronts,
                        }));
                        // `new_branch` came from `Box::into_raw`, so it is never null.
                        (*new_branch).next = InnerNextVerifierNode::Leaf(new_leaf);

                        (new_branch, new_leaf)
                    })
                    .unzip::<_, _, Vec<_>, Vec<_>>();

                branch.next = InnerNextVerifierNode::Branch(new_branches);

                trace!(
                    "racy new_leaves: {:?}",
                    new_leaves
                        .iter()
                        .filter_map(|leaf| {
                            Some(&leaf.as_ref()?.prev.as_ref()?.node.as_ref().value)
                        })
                        .collect::<Vec<_>>()
                );
                trace!("queue before racy: {:?}", queue);
                queue.extend(new_leaves);
                trace!("queue after racy: {:?}", queue);
            }
        }
        Ok(())
    }
}

impl Drop for Explorerer {
    fn drop(&mut self) {
        unsafe {
            // info!("dropping explorerer");
            let mut stack = Vec::new();
            // Every pointer here came from `Box::into_raw`, so none are null.
            for system in self.systems.iter().copied() {
                stack.push((*system).next);
                dealloc(system.cast(), Layout::new::<VerifierConfiguration>());
            }
            #[cfg(debug_assertions)]
            let mut check = (0..100_000).into_iter();
            while let Some(current) = stack.pop() {
                debug_assert!(check.next().is_some());
                match &(*current).next {
                    InnerNextVerifierNode::Branch(branch) => stack.extend_from_slice(branch),
                    InnerNextVerifierNode::Leaf(leaf) => {
                        dealloc(leaf.cast(), Layout::new::<VerifierLeafNode>());
                    }
                }
                dealloc(current.cast(), Layout::new::<VerifierNode>());
            }
        }
    }
}

#[derive(Debug)]
pub enum ExplorePathResult {
    Valid(ValidPathResult),
    Invalid,
    Continue(Explorerer),
}

impl ExplorePathResult {
    pub fn continued(self) -> Option<Explorerer> {
        match self {
            Self::Continue(c) => Some(c),
            _ => None,
        }
    }
    pub fn valid(self) -> Option<ValidPathResult> {
        match self {
            Self::Valid(c) => Some(c),
            _ => None,
        }
    }
    pub fn invalid(self) -> Option<()> {
        match self {
            Self::Invalid => Some(()),
            _ => None,
        }
    }
}

/// An unrecoverable error encountered while running the compiler/verifier.
///
/// These replace the `todo!`/`unimplemented!`/`unreachable!`/`panic!`/`unwrap`/`expect`
/// throws that would otherwise abort the whole process. Instead they are returned in the
/// `Err` of [`Explorerer::next_step`]'s `Result`, so a caller (e.g. a test) can inspect
/// the error *and* the trace of steps leading up to it, rather than having the test binary
/// die without diagnostics.
#[derive(Debug, Clone, PartialEq, Eq, Error)]
pub enum CompilerError {
    /// A construct the verifier does not (yet) support — previously a `todo!` /
    /// `unimplemented!`. The string identifies the unsupported construct.
    #[error("unsupported construct: {0}")]
    Unsupported(String),
    /// An internal invariant the verifier relies on did not hold — previously an
    /// `unwrap` / `expect` / `panic!` / `unreachable!`. The string describes the
    /// invariant that was violated.
    #[error("internal invariant violated: {0}")]
    Internal(String),
}


use std::fmt;
impl fmt::Debug for Explorerer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Explorerer").finish()
    }
}

#[derive(Debug)]
pub struct InvalidPathResult {
    pub complete: bool,
    pub path: String,
    pub explanation: InvalidExplanation,
}

#[derive(Debug)]
pub struct ValidPathResult {
    pub configuration: TypeConfiguration,
    // All the nodes that are touched.
    pub touched: BTreeSet<NonNull<AstNode>>,
    // All the branch nodes that jump.
    pub jumped: BTreeSet<NonNull<AstNode>>,
    /// The byte ranges of each memory region the program accesses at runtime
    /// (see [`AccessedRanges`]). Drives dead-data elimination in codegen: a
    /// descriptor byte outside every range here is only read at compile time
    /// (by the verifier) and its value need not exist in the output program.
    pub accessed: AccessedRanges,
    /// Per-node pointer-arithmetic transitions (see [`AccessTransitions`]).
    /// Drives layout compaction in codegen: unaccessed bytes are *removed* (not
    /// padded) and every instruction that computes an address past them has its
    /// immediate rewritten to the compacted offset.
    pub transitions: AccessTransitions,
    /// Regions that must keep the padded layout (accessed through an
    /// under-determined offset no single immediate rewrite can re-point).
    pub uncompactable: BTreeSet<Label>,
    /// Nodes that must keep their original immediate: they also executed with
    /// a raw address, scalar operand, or range offset — executions invisible to
    /// `transitions` that a rewrite would silently corrupt. Compaction demotes
    /// any region that would require rewriting a pinned node.
    pub pinned_nodes: BTreeSet<NonNull<AstNode>>,
}

impl From<&LabelLocality> for Locality {
    fn from(ll: &LabelLocality) -> Locality {
        match ll {
            LabelLocality::Thread(_) => Locality::Thread,
            LabelLocality::Global => Locality::Global,
        }
    }
}

#[derive(Debug, Error)]
pub enum InvalidExplanation {
    #[error("Could not allocate non-excluded type for {0} for `lat`.")]
    Lat(Label),
    #[error("Could not allocate non-excluded type for {0} for `la`.")]
    La(Label),
    #[error("todo")]
    Sw,
    #[error("todo")]
    Sb,
    #[error("todo")]
    Ld,
    #[error("todo")]
    Lw,
    #[error("todo")]
    Lb,
    #[error("todo")]
    Fail,
}

/// Builds the initial verifier chain for one system: a `start_ptr` node per hart
/// (`root -> hart_{h-1} -> … -> hart_0 -> leaf`), returning the leaf with the given
/// `variable_encounters`. Used to seed exploration in [`Explorerer::new`] and to
/// recreate it in `invalid_path` when a backtracked variable was first encountered
/// at the very first instruction — so its encounter node directly followed the root
/// and there is no predecessor node to re-attach to. Overwrites `root.next`.
unsafe fn build_initial_chain(
    root: *mut VerifierConfiguration,
    start_ptr: NonNull<AstNode>,
    variable_encounters: BTreeMap<Label, *mut VerifierNode>,
) -> Result<*mut VerifierLeafNode, CompilerError> {
    let harts = root
        .as_ref()
        .internal("build_initial_chain: null root")?
        .configuration
        .harts;
    let mut prev = PrevVerifierNode::Root(root);
    let mut hart_fronts = BTreeMap::new();
    for hart in (0..harts).rev() {
        let nonull = Box::into_raw(Box::new(VerifierNode {
            prev,
            root,
            hart,
            node: start_ptr,
            next: InnerNextVerifierNode::Leaf(null_mut()),
        }));
        // `root`/`branch` came from `Box::into_raw`, so are never null.
        match &prev {
            PrevVerifierNode::Root(root) => (**root).next = nonull,
            PrevVerifierNode::Branch(branch) => {
                (**branch).next = InnerNextVerifierNode::Branch(vec![nonull])
            }
        }
        prev = PrevVerifierNode::Branch(nonull);
        hart_fronts.insert(hart, nonull);
    }
    let PrevVerifierNode::Branch(prev) = prev else {
        return Err(CompilerError::Internal(
            "build_initial_chain: no node was created (0 harts)".to_string(),
        ));
    };
    Ok(Box::into_raw(Box::new(VerifierLeafNode {
        prev,
        variable_encounters,
        hart_fronts,
    })))
}

// Get the number of harts of this sub-tree and record the path.
unsafe fn get_backpath_harts(
    prev: *mut VerifierLeafNode,
) -> Result<Vec<usize>, CompilerError> {
    let mut current = prev.as_ref().internal("get_backpath_harts: null leaf")?.prev;
    let mut record = Vec::new();
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let PrevVerifierNode::Branch(branch) =
        current.as_ref().internal("get_backpath_harts: null node")?.prev
    {
        debug_assert!(check.next().is_some());
        let r = match &branch.as_ref().internal("get_backpath_harts: null branch")?.next {
            InnerNextVerifierNode::Branch(branches) => branches
                .iter()
                .position(|&x| x == current)
                .internal("get_backpath_harts: node not found among its parent's branches")?,
            InnerNextVerifierNode::Leaf(_) => {
                return Err(CompilerError::Internal(
                    "get_backpath_harts: leaf where branch expected".to_string(),
                ))
            }
        };
        record.push(r);
        current = branch
    }
    debug_assert!(matches!(
        current
            .as_ref()
            .internal("get_backpath_harts: null node")?
            .prev,
        PrevVerifierNode::Root(_)
    ));
    Ok(record)
}

unsafe fn find_label(node: NonNull<AstNode>, label: &Label) -> Option<NonNull<AstNode>> {
    // Check start
    if let Instruction::Label(LabelInstruction { tag }) = &node.as_ref().as_ref().this {
        if tag == label {
            return Some(node);
        }
    }

    // Trace backwards.
    let mut back = node;
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let Some(prev) = back.as_ref().prev {
        debug_assert!(check.next().is_some());
        if let Instruction::Label(LabelInstruction { tag }) = &prev.as_ref().as_ref().this {
            if tag == label {
                return Some(prev);
            }
        }
        back = prev;
    }

    // Trace forward.
    let mut front = node;
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let Some(next) = front.as_ref().next {
        debug_assert!(check.next().is_some());
        if let Instruction::Label(LabelInstruction { tag }) = &next.as_ref().as_ref().this {
            if tag == label {
                return Some(next);
            }
        }
        front = next;
    }

    None
}

unsafe fn find_state(
    leaf: *mut VerifierLeafNode, // The leaf to finish at.
    configuration: &TypeConfiguration,
) -> Result<State, CompilerError> {
    // info!(
    //     "find_state for {:?} up to {:?}",
    //     leaf.as_ref()
    //         .unwrap()
    //         .prev
    //         .as_ref()
    //         .unwrap()
    //         .root
    //         .as_ref()
    //         .unwrap(),
    //     leaf.as_ref().unwrap().prev.as_ref().unwrap().node.as_ref()
    // );

    let record = get_backpath_harts(leaf)?;
    let root = leaf
        .as_ref()
        .internal("find_state: null leaf")?
        .prev
        .as_ref()
        .internal("find_state: null leaf prev")?
        .root;
    let system = &root.as_ref().internal("find_state: null root")?.configuration;

    // Iterator to generate unique labels.
    const N: u8 = b'z' - b'a';
    let mut tag_iter = (0..)
        .map(|index| Label {
            tag: once('_')
                .chain((0..index / N).map(|_| 'z'))
                .chain(once(char::from((index % N) + b'a')))
                .collect::<String>(),
        })
        .peekable();

    // Iterate forward to find the values.
    let mut state = State::new(system, configuration);
    let mut current = root.as_ref().internal("find_state: null root")?.next;
    for next in record.iter().rev() {
        let vnode = current.as_ref().internal("find_state: null node")?;
        let hart = vnode.hart;
        let hartu = hart as usize;
        match &vnode.node.as_ref().as_ref().this {
            // Instructions with no side affects.
            Instruction::Label(_)
            | Instruction::Blt(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Bne(_)
            | Instruction::Beq(_)
            | Instruction::J(_) => {}
            // No side affects, but worth double checking.
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                let (found_locality, found_type) = state
                    .configuration
                    .get(label)
                    .internal("find_state: define label missing from configuration")?;
                if let Some(defined_locality) = locality {
                    assert_eq!(found_locality, defined_locality);
                }
                if let Some(defined_cast) = cast {
                    assert_eq!(found_type, defined_cast);
                }
            }
            Instruction::Li(Li {
                register,
                immediate,
            }) => {
                let mem_value = MemoryValue::from(*immediate);
                state.registers[hartu]
                    .insert(*register, mem_value)
                    .internal("find_state: li register insert failed")?;
            }
            // TOOD This is the only place where in finding state we need to modify `state.configuration`
            // is this the best way to do this? Could these types not be defined in `next_step` (like `la`)?
            Instruction::Lat(Lat { register, label }) => {
                let (_locality, typeof_type) = state
                    .configuration
                    .get(label)
                    .internal("find_state: lat label missing from configuration")?;
                let (loc, subtypes) = state.memory.set_type(typeof_type, &mut tag_iter, hart);
                // Map the generated descriptor tags (`_a`, …) to the symbols codegen
                // emits for the same records, so runtime reads of descriptor bytes are
                // recorded (in `state.accessed`) under names codegen can look up —
                // this is what lets it elide descriptor bytes never read at runtime.
                state.descriptor_labels.insert(
                    <&Label>::from(&loc).clone(),
                    Label {
                        tag: format!("__{label}_type"),
                    },
                );
                for subtag in subtypes.0.keys() {
                    state.descriptor_labels.insert(
                        subtag.clone(),
                        Label {
                            tag: format!("__{label}_subtypes"),
                        },
                    );
                }
                let ptr = MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                    tag: loc.clone(),
                    offset: MemoryValueU64::ZERO,
                })));
                state.registers[hartu]
                    .insert(*register, ptr)
                    .internal("find_state: lat register insert failed")?;

                // Each type type is thread local and unique between `lat` instructions.
                let hart_type_state = &mut state.configuration;
                hart_type_state.insert(
                    loc.into(),
                    hart,
                    (Locality::Thread, memory_value_type_of()),
                );
                // Extend with subtypes.
                hart_type_state.append(subtypes);
            }
            Instruction::La(La { register, label }) => {
                let (locality, _to_type) = state
                    .configuration
                    .get(label)
                    .internal("find_state: la label missing from configuration")?;
                state.registers[hartu]
                    .insert(
                        *register,
                        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                            tag: match locality {
                                Locality::Global => MemoryLabel::Global {
                                    label: label.clone(),
                                },
                                Locality::Thread => MemoryLabel::Thread {
                                    label: label.clone(),
                                    hart,
                                },
                            },
                            offset: MemoryValueU64::ZERO,
                        }))),
                    )
                    .internal("find_state: la register insert failed")?;
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                find_state_store(&mut state, vnode.node, hartu, to, from, offset, 4)?;
            }
            Instruction::Sb(Sb { to, from, offset }) => {
                find_state_store(&mut state, vnode.node, hartu, to, from, offset, 1)?;
            }
            Instruction::Ld(Ld { to, from, offset }) => {
                find_state_load(&mut state, vnode.node, hartu, to, from, offset, 8)?;
            }
            Instruction::Lw(Lw { to, from, offset }) => {
                find_state_load(&mut state, vnode.node, hartu, to, from, offset, 4)?;
            }
            Instruction::Lb(Lb { to, from, offset }) => {
                find_state_load(&mut state, vnode.node, hartu, to, from, offset, 1)?;
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hartu]
                    .get(lhs)
                    .cloned()
                    .internal("find_state: addi lhs register has no value")?;
                let rhs_value = MemoryValue::from(*rhs);
                let out_value = lhs_value.clone() + rhs_value;
                // Pointer arithmetic: record the transition for layout compaction
                // (this node's immediate is what codegen rewrites when the bytes
                // between `from` and `to` move).
                if let (
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        tag,
                        offset: from_offset,
                    }))),
                    MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                        offset: to_offset, ..
                    }))),
                ) = (&lhs_value, &out_value)
                {
                    let (tag, from_offset, to_offset) =
                        (tag.clone(), from_offset.clone(), to_offset.clone());
                    state.record_transition(vnode.node, &tag, &from_offset, &to_offset);
                } else {
                    // A scalar / raw-address execution of this node: its
                    // immediate is a plain number compaction must never rewrite
                    // (another execution of the same node may be a recorded
                    // pointer transition on a compacted region).
                    state.pinned_nodes.insert(vnode.node);
                }
                state.registers[hartu]
                    .insert(*out, out_value)
                    .internal("find_state: addi register insert failed")?;
            }
            #[allow(unreachable_patterns)]
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hartu]
                        .insert(*dest, MemoryValue::Csr(CsrValue::Mhartid))
                        .internal("find_state: csrr register insert failed")?;
                }
                _ => return Err(CompilerError::Unsupported(format!("csrr from {src:?}"))),
            },
            // TODO Some interrupt state is likely affected here so this needs to be added.
            Instruction::Wfi(_) => {}
            Instruction::Unreachable(_) => {}
            // `#@ <start> <end> <perms>` — declare a memory region the program may
            // access. Takes effect when executed (so e.g. a heap allocator declares
            // each allocation as it makes it), extending the sections that raw-address
            // accesses are validated against in `check_store`/`check_load`. Bounds may
            // be immediates or registers; a register bound contributes its full
            // symbolic range. `end` is exclusive (`size = end - start`).
            Instruction::Region(Region {
                start,
                end,
                permissions,
            }) => {
                let start_value = region_bound_value(&state, hartu, start)?;
                let end_value = region_bound_value(&state, hartu, end)?;
                let region_size = end_value
                    .sub(&start_value)
                    .internal("region: end - start underflowed")?;
                state.memory.sections.push(Section {
                    address: start_value,
                    size: region_size,
                    permissions: Permissions::from(*permissions),
                    volatile: false,
                });
            }
            x => return Err(CompilerError::Unsupported(format!("instruction during state reconstruction: {x:?}"))),
        }
        current = match &current.as_ref().internal("find_state: null node")?.next {
            InnerNextVerifierNode::Branch(b) => b[*next],
            InnerNextVerifierNode::Leaf(_) => {
                return Err(CompilerError::Internal(
                    "find_state: leaf where branch expected".to_string(),
                ))
            }
        };
    }

    // info!(
    //     "hart: {}/{}, state: {:?}",
    //     leaf.as_ref().unwrap().prev.as_ref().unwrap().hart,
    //     leaf.as_ref()
    //         .unwrap()
    //         .prev
    //         .as_ref()
    //         .unwrap()
    //         .root
    //         .as_ref()
    //         .unwrap()
    //         .configuration
    //         .harts,
    //     state
    // );
    Ok(state)
}

impl From<RegionPermissions> for Permissions {
    fn from(p: RegionPermissions) -> Permissions {
        match p {
            RegionPermissions::Read => Permissions::Read,
            RegionPermissions::Write => Permissions::Write,
            RegionPermissions::ReadWrite => Permissions::ReadWrite,
        }
    }
}

/// Evaluates one bound of a `#@` region declaration to its symbolic address.
fn region_bound_value(
    state: &State,
    hartu: usize,
    bound: &RegionBound,
) -> Result<MemoryValueI64, CompilerError> {
    match bound {
        RegionBound::Immediate(immediate) => Ok(MemoryValueI64::from(immediate.value)),
        RegionBound::Register(register) => match state.registers[hartu].get(register) {
            Some(MemoryValue::I64(x)) => Ok(x.clone()),
            x => Err(CompilerError::Unsupported(format!(
                "region bound from register value {x:?}"
            ))),
        },
    }
}

fn find_state_store(
    state: &mut State,
    node: NonNull<AstNode>,
    hartu: usize,
    to: impl Borrow<Register>,
    from: impl Borrow<Register>,
    offset: impl Borrow<Offset>,
    len: u64,
) -> Result<(), CompilerError> {
    let to_value = state.registers[hartu]
        .get(to)
        .internal("store: destination register has no value")?
        .clone();
    let from_value = state.registers[hartu]
        .get(from)
        .internal("store: source register has no value")?
        .clone();
    match &to_value {
        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: to_label,
            offset: to_offset,
        }))) => {
            let (locality, to_type) = state
                .configuration
                .get(<&Label>::from(to_label))
                .internal("store: label missing from configuration")?;
            // We should have already checked the type is large enough for the store.
            let sizeof = size(to_type);
            let final_offset = MemoryValueU64::from(len)
                .add(to_offset)
                .internal("store: offset overflow")?
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.borrow().value.value)
                        .internal("store: negative offset")?,
                ))
                .internal("store: offset overflow")?;
            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(to_label));
            let store_offset = to_offset
                .clone()
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.borrow().value.value)
                        .internal("store: negative offset")?,
                ))
                .internal("store: offset overflow")?;
            // Record the bytes this store can touch at runtime (dead-data analysis)
            // and the pointer→target transition (layout compaction rewrites this
            // node's offset immediate when the bytes between them move).
            state.record_access(to_label, &store_offset, len);
            state.record_transition(node, to_label, to_offset, &store_offset);
            let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                tag: to_label.clone(),
                offset: store_offset,
            }));
            state
                .memory
                .set(&MemoryValue::Ptr(memloc), &len, from_value)
                .internal("store: memory set failed")?;
        }
        MemoryValue::I64(x) => {
            // A raw-address execution: invisible to `transitions`, so the node
            // must keep its original immediate (another execution of the same
            // node may be a pointer access into a compacted region).
            state.pinned_nodes.insert(node);
            // The store's address is the register value plus the instruction offset
            // (`sw t1, 8(t3)` stores at t3+8) — `check_store` validated that address.
            let address = x
                .add(&MemoryValueI64::from(offset.borrow().value.value))
                .internal("store: address overflow")?;
            state
                .memory
                .set(&MemoryValue::I64(address), &len, from_value)
                .internal("store: memory set failed")?;
        }
        x => return Err(CompilerError::Unsupported(format!("store to {x:?}"))),
    }
    Ok(())
}

fn find_state_load(
    state: &mut State,
    node: NonNull<AstNode>,
    hartu: usize,
    to: impl Borrow<Register>,
    from: impl Borrow<Register>,
    offset: impl Borrow<Offset>,
    len: u64,
) -> Result<(), CompilerError> {
    let from_value = state.registers[hartu]
        .get(from)
        .internal("load: source register has no value")?
        .clone();
    match &from_value {
        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: from_label,
            offset: from_offset,
        }))) => {
            let (locality, from_type) = state
                .configuration
                .get(<&Label>::from(from_label))
                .internal("load: label missing from configuration")?;
            // We should have already checked the type is large enough for the load.
            let sizeof = size(from_type);
            let final_offset = MemoryValueU64::from(len)
                .add(from_offset)
                .internal("load: offset overflow")?
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.borrow().value.value)
                        .internal("load: negative offset")?,
                ))
                .internal("load: offset overflow")?;

            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(from_label));

            let memloc = Slice {
                base: from_label.clone(),
                offset: from_offset
                    .clone()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.borrow().value.value)
                            .internal("load: negative offset")?,
                    ))
                    .internal("load: offset overflow")?,
                len,
            };
            // Record the bytes this load can touch at runtime (dead-data analysis)
            // and the pointer→target transition (layout compaction rewrites this
            // node's offset immediate when the bytes between them move).
            state.record_access(&memloc.base, &memloc.offset, len);
            state.record_transition(node, &memloc.base, from_offset, &memloc.offset);
            let value = state.memory.get(&memloc).internal("load: memory get failed")?;
            state.registers[hartu]
                .insert(to.borrow().clone(), value)
                .internal("load: register insert failed")?;
        }
        // A raw-address load — a region described by the system configuration or
        // declared with `#@` (validated by `check_load`). The backing memory is
        // not modelled precisely, so the loaded value is the full range of the
        // loaded width: a sound over-approximation of whatever was stored there.
        MemoryValue::I64(_) => {
            // Raw execution: the node must keep its original immediate (see the
            // store arm).
            state.pinned_nodes.insert(node);
            let value = match len {
                1 => MemoryValue::from(Type::I8),
                4 => MemoryValue::from(Type::I32),
                8 => MemoryValue::from(Type::I64),
                _ => {
                    return Err(CompilerError::Unsupported(format!(
                        "load of width {len} from a raw address"
                    )))
                }
            };
            state.registers[hartu]
                .insert(to.borrow().clone(), value)
                .internal("load: register insert failed")?;
        }
        x => return Err(CompilerError::Unsupported(format!("load from {x:?}"))),
    }
    Ok(())
}
