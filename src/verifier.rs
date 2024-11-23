use crate::ast::*;
use crate::verifier_types::*;
use itertools::Itertools;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::borrow::Borrow;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::once;
use std::ptr::null_mut;
use std::{collections::VecDeque, ptr::NonNull};
use thiserror::Error;
use tracing::error;
use tracing::trace;
use tracing::warn;

use std::collections::HashSet;
use tracing::info;

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
    pub last_out: Option<TypeConfiguration>,
    #[cfg(debug_assertions)]
    pub counter: usize,
    /// Program configurations that have been found to be invalid.
    #[cfg(debug_assertions)]
    pub excluded: BTreeSet<TypeConfiguration>,
    /// Pointer to the 2nd element in the AST (e.g. it skips the 1st which is `.global _start`).
    pub second_ptr: NonNull<AstNode>,
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
    ) -> Self {
        // You cannot verify a program that starts running on 0 harts.
        assert!(systems.iter().all(|x| x.harts > 0));

        // Intial misc stuff
        let first = ast.unwrap().as_ref();
        let second_ptr = first.next.unwrap();
        let second = second_ptr.as_ref();
        match &first.as_ref().this {
            Instruction::Global(Global { tag: start_tag }) => match &second.as_ref().this {
                Instruction::Label(LabelInstruction { tag }) => {
                    assert_eq!(start_tag, tag);
                }
                _ => panic!("The second node must be the start label"),
            },
            _ => panic!("The first node must be the global start label definition"),
        }

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
        // for each hart, the ordering of these initial nodes doesn't matter (as they are all `_start`).
        let queue = systems
            .iter().copied()
            .map(|root| {
                let harts = (*root).configuration.harts;
                // All harts are intiailized as `_start`.
                let mut prev = PrevVerifierNode::Root(root);
                let mut hart_fronts = BTreeMap::new();
                for hart in (0..=harts as u8).rev() {
                    let nonull = Box::into_raw(Box::new(VerifierNode {
                        prev,
                        root: root,
                        hart,
                        node: second_ptr,
                        next: InnerNextVerifierNode::Leaf(null_mut()),
                    }));

                    match &prev {
                        PrevVerifierNode::Root(root) => {
                            debug_assert!(root.as_ref().unwrap().next.is_null());
                            root.as_mut().unwrap().next = nonull;
                        },
                        PrevVerifierNode::Branch(branch) => {
                            debug_assert!(matches!(branch.as_ref().unwrap().next,InnerNextVerifierNode::Leaf(leaf) if leaf.is_null()));
                            branch.as_mut().unwrap().next = InnerNextVerifierNode::Branch(vec![nonull]);
                        }
                    }
                    prev = PrevVerifierNode::Branch(nonull);
                    hart_fronts.insert(hart, nonull);
                }
                let PrevVerifierNode::Branch(prev) = prev else { unreachable!() };
                let leaf = Box::into_raw(Box::new(VerifierLeafNode {
                    prev,
                    variable_encounters: BTreeMap::new(),
                    hart_fronts,
                }));

                leaf
            })
            .collect::<VecDeque<_>>();

        // We return the explorer and it's contained state.
        #[cfg(debug_assertions)]
        let x = Self {
            last_out: None,
            systems,
            second_ptr,
            excluded,
            configuration,
            touched,
            queue,
            jumped,
            types: Default::default(),
            encountered: Default::default(),
            counter: 0,
        };
        #[cfg(not(debug_assertions))]
        let x = Self {
            systems,
            second_ptr,
            configuration,
            touched,
            queue,
            jumped,
            types: Default::default(),
            encountered: Default::default(),
        };
        return x;
    }

    // Advance the verifier by one instruction.
    pub unsafe fn next_step(mut self) -> ExplorePathResult {
        #[cfg(debug_assertions)]
        {
            self.counter += 1;
            
            if let Some(old) = &mut self.last_out {
                if *old != self.configuration {
                    info!("{}",self.configuration);
                    *old = self.configuration.clone();
                }
                
            }
            else {
                info!("{}",self.configuration);
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
                .map(|ptr| ptr.as_ref().unwrap())
                .collect::<Vec<_>>()
        );

        // Get the next node to explore.
        let Some(leaf_ptr) = self.queue.front().copied() else {
            return ExplorePathResult::Valid(ValidPathResult {
                configuration: self.configuration.clone(),
                touched: self.touched.clone(),
                jumped: self.jumped.clone(),
            });
        };

        // Get some data.
        let leaf = leaf_ptr.as_mut().unwrap();
        trace!("leaf: {leaf:?}");
        let branch = leaf.prev.as_ref().unwrap();
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
            | Instruction::Branch(_)
            | Instruction::Beq(_)
            | Instruction::J(_) => {}
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
                self = match self.check_store(leaf_ptr, branch, to, offset, 4) {
                    Ok(x) => x,
                    Err(err) => return err,
                };
            }
            Instruction::Sb(Sb {
                to,
                from: _,
                offset,
            }) => {
                self = match self.check_store(leaf_ptr, branch, to, offset, 1) {
                    Ok(x) => x,
                    Err(err) => return err,
                };
            }
            // TODO A lot of the checking loads code is duplicated, reduce this duplication.
            // For any load we need to validate the destination is valid.
            Instruction::Ld(Ld {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 8) {
                    Ok(x) => x,
                    Err(err) => return err,
                };
            }
            Instruction::Lw(Lw {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 4) {
                    Ok(x) => x,
                    Err(err) => return err,
                };
            }
            Instruction::Lb(Lb {
                to: _,
                from,
                offset,
            }) => {
                self = match self.check_load(leaf_ptr, branch, from, offset, 1) {
                    Ok(x) => x,
                    Err(err) => return err,
                };
            }
            // If any fail is encountered then the path is invalid.
            Instruction::Fail(_) => {
                info!("hit fail {:?}", ast.as_ref());
                return self.outer_invalid_path();
            }
            x => todo!("{x:?}"),
        }
        self.queue_up(leaf_ptr);
        // The leaf has to maintain it's position at the front of the queue until we queue up new
        // nodes or we backtrace along an invalid path, when an invalid path is encountered we call
        // `outer_invalid_path` which calls `invalid_path` which will deallocate the leaf and set
        // new leaves (and return and never reach this statement).
        // When we only queue up new leaves, the current leaf remains so we need to pop it off here.
        self.queue.pop_front();

        return ExplorePathResult::Continue(self);
    }

    /// When an invalid path is encountered we need to backtrack from where we can start exploring a
    /// new path. To do this we iterate across all leaves and de-allocate back up 1st encounter of
    /// the last encountered variable (such that we can then try a new path where this variable has
    /// different type infomation).
    /// 1. Pop most recently encountered variable.
    /// 2. De-allocate all nodes below
    pub unsafe fn outer_invalid_path(mut self) -> ExplorePathResult {
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
            self.invalid_path(&recent);

            // Check if there any other possible types for this variable
            let is_empty = {
                let iter = self.types.get(&recent).unwrap();
                debug_assert_eq!(iter.size_hint().0, iter.size_hint().1.unwrap());
                iter.size_hint().0 == 0
            };

            // Remove the iterator if there are no other possible types to explore.
            if is_empty {
                self.types.remove(&recent);
                continue;
            }

            // If there are more possible types, push the variables back to encountered.
            self.encountered.push(recent);
            return ExplorePathResult::Continue(self);
        }
        // Everything is deallocated when `self` is dropped.
        return ExplorePathResult::Invalid;
    }

    pub unsafe fn invalid_path(&mut self, recent: &Label) {
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
        let mut encounters: BTreeMap<*mut VerifierNode, BTreeMap<Label, *mut VerifierNode>> =
            BTreeMap::new();
        let mut unchanged = VecDeque::new();
        for leaf in self.queue.iter().copied() {
            // Multiple leafs might have the same 1st encounter, in this case these leafs might
            // encounter different variables later, but for encounters before the shared encounter
            // they will all be the same. Given 2 leafs with encounters [a: 1, b: 3, d: 6] and
            // [a: 1, b: 3, d:5] the new leaf that should exist after their deallocation should have
            // only contain encounters that happened before the shared encounter e.g. [a: 1], we can
            // easily determine this by the using the intersection of all encounters (retain where
            // they have the same variable encountered at the same place).
            let mut map = leaf.as_ref().unwrap().variable_encounters.clone();
            if let Some(encounter) = map.remove(&recent) {
                encounters
                    .entry(encounter)
                    .and_modify(|ve| ve.retain(|k, v| map.get(k) == Some(v)))
                    .or_insert(map);
            } else {
                unchanged.push_back(leaf);
            }
        }

        // Set the queue to the leafs which haven't encountered the variable.
        // We will append new leafs later in this scope as leafs to replace the leafs we deallocate.
        self.queue = unchanged;

        // Iterate across leafs we need to deallocate.
        for (encounter_ptr, variable_encounters) in encounters {
            // We can `unwrap` here since every path will have `_start` nodes for every heart that
            // will prevent an encounter ever following a root.
            let encounter_ref = encounter_ptr.as_ref().unwrap();
            // Store previous node.
            let current = *encounter_ref.prev.branch().unwrap();
            let root = encounter_ref.root;
            let harts = root.as_ref().unwrap().configuration.harts;

            // De-allocate the 1st encounter for this variable.
            let mut stack = vec![encounter_ptr];
            while let Some(next) = stack.pop() {
                match &next.as_ref().unwrap().next {
                    InnerNextVerifierNode::Branch(branches) => {
                        stack.extend(branches);
                    }
                    InnerNextVerifierNode::Leaf(leaf) => {
                        dealloc(leaf.cast(), Layout::new::<VerifierLeafNode>());
                    }
                }
                dealloc(next.cast(), Layout::new::<VerifierLeafNode>());
            }

            // Get new hart fronts
            let mut prev = current;
            let mut hart_fronts = BTreeMap::new();
            loop {
                let branch_ptr = prev;
                let branch_ref = branch_ptr.as_ref().unwrap();
                hart_fronts.entry(branch_ref.hart).or_insert(branch_ptr);
                if hart_fronts.len() == harts as usize {
                    break;
                }
                // We can `unwrap` here since it should be guranteed that every path has a node for
                // every hart which will ensure `hart_fronts.len() == harts as usize` before hitting
                // the root.
                prev = *branch_ref.prev.branch().unwrap();
            }

            // Set new leaf node.
            // The `encounter.prev` will never be a root since the `_start` nodes follow the root.
            let new_leaf = Box::into_raw(Box::new(VerifierLeafNode {
                prev: current,
                variable_encounters,
                hart_fronts: hart_fronts,
            }));
            current.as_mut().unwrap().next = InnerNextVerifierNode::Leaf(new_leaf);
            self.queue.push_back(new_leaf);
        }
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
        self,
        leaf_ptr: *mut VerifierLeafNode,
        branch: impl Borrow<VerifierNode>,
        to: impl Borrow<Register>,
        offset: impl Borrow<crate::ast::Offset>,
        type_size: u64,
    ) -> Result<Self, ExplorePathResult> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration);

        // Check the destination is valid.
        match state.registers[branch.borrow().hart as usize].get(to) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) =
                    state.configuration.get(<&Label>::from(from_label)).unwrap();
                // If attempting to access outside the memory space for the label.
                let full_offset = MemoryValueU64::from(type_size)
                    .add(from_offset)
                    .unwrap()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.borrow().value.value).unwrap(),
                    ))
                    .unwrap();
                let size = size(ttype);

                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
                        info!("reached invalid store in path due to attempting to accress memory space past a label, size: {size:?}, offset: {full_offset:?}, node: {:?}", branch.borrow().node.as_ref().value);
                        Err(self.outer_invalid_path())
                    }
                    true => {
                        // Else we found the label and we can validate that the loading
                        // of a word with the given offset is within the address space.
                        // So we continue exploration.
                        Ok(self)
                    }
                }
            }
            // For acceses to main memory, we need to validate this is in `sections`.
            Some(MemoryValue::I64(x)) => {
                let start = x
                    .add(&MemoryValueI64::from(offset.borrow().value.value))
                    .unwrap();
                let sections = &branch
                    .borrow()
                    .root
                    .as_ref()
                    .unwrap()
                    .configuration
                    .sections;

                // Find a section that the store would be within.
                let section_opt = sections.iter().find(|s| {
                    let required_size = start
                        .sub(&s.address)
                        .unwrap()
                        .add(&MemoryValueI64::from(i64::try_from(type_size).unwrap()))
                        .unwrap();
                    match (start.compare(&s.address), s.size.compare(&required_size)) {
                        (
                            RangeOrdering::Greater | RangeOrdering::Equal | RangeOrdering::Matches,
                            RangeOrdering::Less | RangeOrdering::Equal | RangeOrdering::Matches,
                        ) => true,
                        (RangeOrdering::Less | RangeOrdering::Cover, _) => false,
                        (_, RangeOrdering::Greater | RangeOrdering::Cover) => false,
                        _ => todo!(),
                    }
                });

                // Check this section supports writing.
                if let Some(section) = section_opt {
                    match section.permissions {
                        Permissions::ReadWrite | Permissions::Write => Ok(self),
                        Permissions::Read => {
                            info!("reached invalid path due to attempt to write to read-only");
                            Err(self.outer_invalid_path())
                        },
                    }
                } else {
                    info!("reached invalid path due to attempt to write to undescribed memory");
                    Err(self.outer_invalid_path())
                }
            }
            x => todo!("{x:?}"),
        }
    }

    /// Verifies a load is valid for a given configuration.
    unsafe fn check_load(
        self,
        leaf_ptr: *mut VerifierLeafNode,
        branch: impl Borrow<VerifierNode>,
        from: impl Borrow<Register>,
        offset: impl Borrow<crate::ast::Offset>,
        type_size: u64,
    ) -> Result<Self, ExplorePathResult> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration);

        // Check the destination is valid.
        match state.registers[branch.borrow().hart as usize].get(from) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) =
                    state.configuration.get(<&Label>::from(from_label)).unwrap();

                // If attempting to access outside the memory space for the label.
                let offset_value = offset.borrow().value.value;
                let full_offset = MemoryValueU64::from(type_size)
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset_value).unwrap(),
                    ))
                    .unwrap()
                    .add(from_offset)
                    .unwrap();
                let size = size(ttype);
                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
                        info!("reached invalid load in path due to attempting to accress memory space past a label, size: {size:?}, offset: {full_offset:?} ({type_size:?} + {offset_value} + {from_offset:?}), node: {:?}", branch.borrow().node.as_ref().value);
                        return Err(self.outer_invalid_path());
                    }
                    true => {
                        // Else, we found the label and we can validate that the loading
                        // of a word with the given offset is within the address space.
                        // So we continue exploration.
                        Ok(self)
                    }
                }
            }
            x => todo!("{x:?}"),
        }
    }

    /// Queues up the next node to evaluate.
    ///
    /// We look at the next node for the 1st hart and queue this up if its not racy,
    /// if its racy, we look at the 2nd hart and queue it up if its not racy,
    /// if its racy we look at the 3rd hart etc. If all next nodes are racy, we queue
    /// up all racy instructions (since we need to evaluate all the possible ordering of them).
    unsafe fn queue_up(&mut self, leaf_ptr: *mut VerifierLeafNode) {
        let queue = &mut self.queue;
        let configuration = &mut self.configuration;
        let jumped = &mut self.jumped;
        // TOOD We duplicate so much work doing `find_state` in a bunch of places and
        // multiple times when the state hasn't change, we should avoid doing this call
        // here (and remove it in other places too).
        let state = find_state(leaf_ptr, configuration);
        let leaf = leaf_ptr.as_mut().unwrap();

        // Search the verifier tree for the fronts of all harts.
        let mut fronts = BTreeMap::new();
        let mut current = leaf.prev.as_ref().unwrap();
        let harts = current.root.as_ref().unwrap().configuration.harts;
        fronts.insert(current.hart, current.node);
        #[cfg(debug_assertions)]
        let mut check = (0..1000).into_iter();
        while fronts.len() < harts as usize {
            debug_assert!(check.next().is_some());
            let PrevVerifierNode::Branch(branch) = current.prev else {
                unreachable!()
            };
            current = branch.as_ref().unwrap();
            fronts.entry(current.hart).or_insert(current.node);
        }

        // debug!(
        //     "fronts: {:?}",
        //     fronts
        //         .iter()
        //         .map(|(hart, ast)| (hart, ast.as_ref().as_ref().this.to_string()))
        //         .collect::<BTreeMap<_, _>>()
        // );

        let followup = |node: NonNull<AstNode>,
                        hart: u8|
         -> Option<Result<(u8, NonNull<AstNode>), (u8, NonNull<AstNode>)>> {
            let instruction = &node.as_ref().as_ref().this;
            match instruction {
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
                | Instruction::Branch(_)
                | Instruction::Beq(_)
                | Instruction::J(_) => Some(Err((hart, node))),
                // Possibly racy.
                // If the label is thread local its not racy.
                Instruction::Sb(Sb { to: register, .. })
                | Instruction::Sw(Sw { to: register, .. })
                | Instruction::Ld(Ld { from: register, .. })
                | Instruction::Lw(Lw { from: register, .. })
                | Instruction::Lb(Lb { from: register, .. }) => {
                    let value = state.registers[hart as usize].get(register).unwrap();
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
                        _ => todo!("instruction: {instruction:?} value: {value:?}"),
                    }
                }
                // See note on `wfi`.
                Instruction::Wfi(_) => Some(Ok((hart, node))),
                Instruction::Unreachable(_) => None,
                x => todo!("{x:?}"),
            }
        };

        // The lowest hart non-racy node is enqueued.
        // (or possibly multiples nodes in the case of a conditional jump where
        // we cannot deteremine the condition).

        let next_nodes = fronts
            .iter()
            // TODO Document why reverse order is important here.
            .rev()
            .filter_map(|(&hart, &node)| {
                let node_ref = node.as_ref();
                match &node_ref.as_ref().this {
                    // Conditional.
                    Instruction::Blt(Blt { rhs, lhs, label }) => {
                        let lhs = state.registers[hart as usize].get(lhs).unwrap();
                        let rhs = state.registers[hart as usize].get(rhs).unwrap();
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Less) => {
                                jumped.insert(node);
                                let label_node = find_label(node, label).unwrap();
                                followup(label_node, hart)
                            }
                            Some(RangeOrdering::Greater | RangeOrdering::Equal) => {
                                followup(node_ref.next.unwrap(), hart)
                            }
                            _ => todo!(),
                        }
                    }
                    Instruction::Beq(Beq { rhs, lhs, out }) => {
                        let lhs = state.registers[hart as usize].get(lhs).unwrap();
                        let rhs = state.registers[hart as usize].get(rhs).unwrap();
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Equal) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out).unwrap();
                                followup(label_node, hart)
                            }
                            Some(RangeOrdering::Greater | RangeOrdering::Less) => {
                                followup(node_ref.next.unwrap(), hart)
                            }
                            _ => todo!(),
                        }
                    }
                    Instruction::Bne(Bne { rhs, lhs, out }) => {
                        let lhs = state.registers[hart as usize].get(lhs).unwrap();
                        let rhs = state.registers[hart as usize].get(rhs).unwrap();
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Greater | RangeOrdering::Less) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out).unwrap();
                                trace!("bne jumped: {:?}", label_node.as_ref().value);
                                followup(label_node, hart)
                            }
                            Some(RangeOrdering::Equal) => {
                                trace!("bne no jump");
                                followup(node_ref.next.unwrap(), hart)
                            }
                            _ => todo!(),
                        }
                    }
                    Instruction::Bnez(Bnez { src, dest }) => {
                        let src = state.registers[hart as usize].get(src).unwrap();

                        // In the case the path is determinate, we either queue up the label
                        // or the next ast node and don't need to actually visit/evaluate
                        // the branch at runtime.
                        match src {
                            MemoryValue::I8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        followup(node_ref.next.unwrap(), hart)
                                    } else {
                                        todo!()
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest).unwrap();
                                    followup(label_node, hart)
                                }
                            },
                            MemoryValue::U8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        followup(node_ref.next.unwrap(), hart)
                                    } else {
                                        todo!()
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest).unwrap();
                                    followup(label_node, hart)
                                }
                            },
                            MemoryValue::Csr(CsrValue::Mhartid) => {
                                if hart == 0 {
                                    followup(node_ref.next.unwrap(), hart)
                                } else {
                                    jumped.insert(node);
                                    let label_node = find_label(node, dest).unwrap();
                                    followup(label_node, hart)
                                }
                            }
                            x => todo!("{x:?}"),
                        }
                    }
                    Instruction::Beqz(Beqz { register, label }) => {
                        let src = state.registers[hart as usize].get(register).unwrap();

                        // In the case the path is determinate, we either queue up the label
                        // or the next ast node and don't need to actually visit/evaluate
                        // the branch at runtime.
                        match src {
                            MemoryValue::U8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        jumped.insert(node);
                                        let label_node = find_label(node, label).unwrap();
                                        followup(label_node, hart)
                                    } else {
                                        todo!()
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            },
                            MemoryValue::I8(imm) => match imm.compare_scalar(&0) {
                                RangeScalarOrdering::Within => {
                                    if imm.eq(&0) {
                                        jumped.insert(node);
                                        let label_node = find_label(node, label).unwrap();
                                        followup(label_node, hart)
                                    } else {
                                        todo!()
                                    }
                                }
                                RangeScalarOrdering::Greater | RangeScalarOrdering::Less => {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            },
                            MemoryValue::Csr(CsrValue::Mhartid) => {
                                if hart == 0 {
                                    jumped.insert(node);
                                    let label_node = find_label(node, label).unwrap();
                                    followup(label_node, hart)
                                } else {
                                    followup(node_ref.next.unwrap(), hart)
                                }
                            }
                            x => todo!("{x:?}"),
                        }
                    }
                    Instruction::Bge(Bge { lhs, rhs, out }) => {
                        let lhs = state.registers[hart as usize].get(lhs).unwrap();
                        let rhs = state.registers[hart as usize].get(rhs).unwrap();
                        match lhs.compare(rhs) {
                            Some(RangeOrdering::Greater | RangeOrdering::Equal) => {
                                jumped.insert(node);
                                let label_node = find_label(node, out).unwrap();
                                followup(label_node, hart)
                            }
                            Some(RangeOrdering::Less) => followup(node_ref.next.unwrap(), hart),
                            _ => todo!(),
                        }
                    }
                    Instruction::J(J { dest }) => {
                        jumped.insert(node);
                        let label_node = find_label(node, dest).unwrap();
                        followup(label_node, hart)
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
                    | Instruction::Fail(_) => followup(node_ref.next.unwrap(), hart),
                    Instruction::Branch(Branch { out }) => {
                        let label_node = find_label(node, out).unwrap();
                        followup(label_node, hart)
                    }
                    // See note on `wfi`.
                    Instruction::Wfi(_) => Some(Ok((hart, node_ref.next.unwrap()))),
                    // Blocking.
                    Instruction::Unreachable(_) => None,
                    x => todo!("{x:?}"),
                }
            })
            .collect::<Result<Vec<_>, _>>();

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
                let branch = branch_ptr.as_mut().unwrap();
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
                let branch = branch_ptr.as_mut().unwrap();
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
                        new_branch.as_mut().unwrap().next = InnerNextVerifierNode::Leaf(new_leaf);

                        (new_branch, new_leaf)
                    })
                    .unzip::<_, _, Vec<_>, Vec<_>>();

                branch.next = InnerNextVerifierNode::Branch(new_branches);

                trace!(
                    "racy new_leaves: {:?}",
                    new_leaves
                        .iter()
                        .map(|leaf| &leaf
                            .as_ref()
                            .unwrap()
                            .prev
                            .as_ref()
                            .unwrap()
                            .node
                            .as_ref()
                            .value)
                        .collect::<Vec<_>>()
                );
                trace!("queue before racy: {:?}", queue);
                queue.extend(new_leaves);
                trace!("queue after racy: {:?}", queue);
            }
        }
    }
}

impl Drop for Explorerer {
    fn drop(&mut self) {
        unsafe {
            // info!("dropping explorerer");
            let mut stack = Vec::new();
            for system in self.systems.iter().copied() {
                stack.push(system.as_ref().unwrap().next);
                dealloc(system.cast(), Layout::new::<VerifierConfiguration>());
            }
            #[cfg(debug_assertions)]
            let mut check = (0..100_000).into_iter();
            while let Some(current) = stack.pop() {
                debug_assert!(check.next().is_some());
                match &current.as_ref().unwrap().next {
                    InnerNextVerifierNode::Branch(branch) => stack.extend_from_slice(&branch),
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

// Get the number of harts of this sub-tree and record the path.
unsafe fn get_backpath_harts(prev: *mut VerifierLeafNode) -> Vec<usize> {
    let mut current = prev.as_ref().unwrap().prev;
    let mut record = Vec::new();
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let PrevVerifierNode::Branch(branch) = current.as_ref().unwrap().prev {
        debug_assert!(check.next().is_some());
        let r = match &branch.as_ref().unwrap().next {
            InnerNextVerifierNode::Branch(branches) => {
                branches.iter().position(|&x| x == current).unwrap()
            }
            InnerNextVerifierNode::Leaf(_) => unreachable!(),
        };
        record.push(r);
        current = branch
    }
    assert!(matches!(
        current.as_ref().unwrap().prev,
        PrevVerifierNode::Root(_)
    ));
    record
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
) -> State {
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

    let record = get_backpath_harts(leaf);
    let root = leaf.as_ref().unwrap().prev.as_ref().unwrap().root;
    let system = &root.as_ref().unwrap().configuration;

    // Iterator to generate unique labels.
    const N: u8 = b'z' - b'a';
    let mut tag_iter = (0..)
        .map(|index| Label {
            tag: once('_')
                .chain((0..index / N).map(|_| 'z'))
                .chain(once(char::from_u32(((index % N) + b'a') as u32).unwrap()))
                .collect::<String>(),
        })
        .peekable();

    // Iterate forward to find the values.
    let mut state = State::new(system, configuration);
    let mut current = root.as_ref().unwrap().next;
    for next in record.iter().rev() {
        let vnode = current.as_ref().unwrap();
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
            | Instruction::Branch(_)
            | Instruction::Beq(_)
            | Instruction::J(_) => {}
            // No side affects, but worth double checking.
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                let (found_locality, found_type) = state.configuration.get(label).unwrap();
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
                state.registers[hartu].insert(*register, mem_value).unwrap();
            }
            // TOOD This is the only place where in finding state we need to modify `state.configuration`
            // is this the best way to do this? Could these types not be defined in `next_step` (like `la`)?
            Instruction::Lat(Lat { register, label }) => {
                let (_locality, typeof_type) = state.configuration.get(label).unwrap();
                let (loc, subtypes) = state.memory.set_type(typeof_type, &mut tag_iter, hart);
                let ptr = MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                    tag: loc.clone(),
                    offset: MemoryValueU64::ZERO,
                })));
                state.registers[hartu].insert(*register, ptr).unwrap();

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
                let (locality, _to_type) = state.configuration.get(label).unwrap();
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
                    .unwrap();
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                find_state_store(&mut state, hartu, to, from, offset, 4);
            }
            Instruction::Sb(Sb { to, from, offset }) => {
                find_state_store(&mut state, hartu, to, from, offset, 1);
            }
            Instruction::Ld(Ld { to, from, offset }) => {
                find_state_load(&mut state, hartu, to, from, offset, 8);
            }
            Instruction::Lw(Lw { to, from, offset }) => {
                find_state_load(&mut state, hartu, to, from, offset, 4);
            }
            Instruction::Lb(Lb { to, from, offset }) => {
                find_state_load(&mut state, hartu, to, from, offset, 1);
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hartu].get(lhs).cloned().unwrap();
                let rhs_value = MemoryValue::from(*rhs);
                let out_value = lhs_value + rhs_value;
                state.registers[hartu].insert(*out, out_value).unwrap();
            }
            #[allow(unreachable_patterns)]
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hartu]
                        .insert(*dest, MemoryValue::Csr(CsrValue::Mhartid))
                        .unwrap();
                }
                _ => todo!(),
            },
            // TODO Some interrupt state is likely affected here so this needs to be added.
            Instruction::Wfi(_) => {}
            Instruction::Unreachable(_) => {}
            x => todo!("{x:?}"),
        }
        current = match &current.as_ref().unwrap().next {
            InnerNextVerifierNode::Branch(b) => b[*next],
            InnerNextVerifierNode::Leaf(_) => unreachable!(),
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
    state
}

fn find_state_store(
    state: &mut State,
    hartu: usize,
    to: impl Borrow<Register>,
    from: impl Borrow<Register>,
    offset: impl Borrow<Offset>,
    len: u64,
) {
    let Some(to_value) = state.registers[hartu].get(to) else {
        todo!()
    };
    let Some(from_value) = state.registers[hartu].get(from) else {
        todo!()
    };
    match to_value {
        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: to_label,
            offset: to_offset,
        }))) => {
            let (locality, to_type) = state.configuration.get(<&Label>::from(to_label)).unwrap();
            // We should have already checked the type is large enough for the store.
            let sizeof = size(to_type);
            let final_offset = MemoryValueU64::from(len)
                .add(to_offset)
                .unwrap()
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.borrow().value.value).unwrap(),
                ))
                .unwrap();
            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(to_label));
            let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                tag: to_label.clone(),
                offset: to_offset
                    .clone()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.borrow().value.value).unwrap(),
                    ))
                    .unwrap(),
            }));
            state
                .memory
                .set(&MemoryValue::Ptr(memloc), &len, from_value.clone())
                .unwrap();
        }
        MemoryValue::I64(x) => {
            state
                .memory
                .set(&MemoryValue::I64(*x), &len, from_value.clone())
                .unwrap();
        }
        _ => todo!(),
    }
}

fn find_state_load(
    state: &mut State,
    hartu: usize,
    to: impl Borrow<Register>,
    from: impl Borrow<Register>,
    offset: impl Borrow<Offset>,
    len: u64,
) {
    let Some(from_value) = state.registers[hartu].get(from) else {
        todo!()
    };
    match from_value {
        MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
            tag: from_label,
            offset: from_offset,
        }))) => {
            let (locality, from_type) =
                state.configuration.get(<&Label>::from(from_label)).unwrap();
            // We should have already checked the type is large enough for the load.
            let sizeof = size(from_type);
            let final_offset = MemoryValueU64::from(len)
                .add(from_offset)
                .unwrap()
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.borrow().value.value).unwrap(),
                ))
                .unwrap();

            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(from_label));

            let memloc = Slice {
                base: from_label.clone(),
                offset: from_offset
                    .clone()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.borrow().value.value).unwrap(),
                    ))
                    .unwrap(),
                len,
            };
            let value = state.memory.get(&memloc).unwrap();
            state.registers[hartu]
                .insert(to.borrow().clone(), value)
                .unwrap();
        }
        x => todo!("{x:?}"),
    }
}
