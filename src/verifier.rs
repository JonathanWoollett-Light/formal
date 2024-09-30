use crate::ast::*;
use crate::verifier_types::*;
use itertools::intersperse;
use std::alloc::Layout;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::iter::once;
use std::ops::Range;
use std::ptr;
use std::rc::Rc;
use std::{alloc::alloc, collections::VecDeque, ptr::NonNull};
use thiserror::Error;
use tracing::debug;
use tracing::error;
use tracing::trace;

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

use std::alloc::dealloc;

/// Contains the configuration of the system
pub struct VerifierConfiguration {
    pub harts: u8,
    pub next: NonNull<VerifierNode>,
}

enum PrevVerifierNode {
    Root(NonNull<VerifierConfiguration>),
    Branch(NonNull<VerifierNode>),
}
impl PrevVerifierNode {
    fn branch(&self) -> Option<&NonNull<VerifierNode>> {
        match self {
            Self::Branch(branch) => Some(branch),
            Self::Root(_) => None,
        }
    }
}

pub enum InnerNextVerifierNode {
    Branch(Vec<NonNull<VerifierNode>>),
    Leaf(NonNull<VerifierLeafNode>),
}

/// We use a tree to trace the execution of the program,
/// then when conditions are required it can resolve them
/// by looking back at the trace.
pub struct VerifierNode {
    // The previous node in global execution.
    pub prev: PrevVerifierNode,
    pub root: NonNull<VerifierConfiguration>,
    // Current hart.
    pub hart: u8,
    pub node: NonNull<AstNode>,
    pub next: InnerNextVerifierNode,
}

enum OuterVerifierNode {
    Leaf(VerifierLeafNode),
    Branch(VerifierNode),
}

impl Drop for Explorerer {
    fn drop(&mut self) {
        unsafe {
            let mut stack = Vec::new();
            for root in &self.roots {
                stack.push(root.as_ref().next);
                dealloc(root.as_ptr().cast(), Layout::new::<VerifierConfiguration>());
            }
            while let Some(current) = stack.pop() {
                match &current.as_ref().next {
                    InnerNextVerifierNode::Branch(branch) => stack.extend_from_slice(&branch),
                    InnerNextVerifierNode::Leaf(leaf) => {
                        dealloc(leaf.as_ptr().cast(), Layout::new::<VerifierLeafNode>());
                    }
                }
                dealloc(current.as_ptr().cast(), Layout::new::<VerifierNode>());
            }
        }
    }
}
use std::sync::Arc;

// TODO Support some amount of state caching so it doesn't need to re-traverse the whole tree each step to find state.
struct VerifierLeafNode {
    // The previous node.
    pub prev: NonNull<VerifierNode>,
    // The nodes where variables where first encountered.
    pub variable_encounters: BTreeMap<Label, NonNull<VerifierNode>>,
    // The most recent node for each hart.
    pub hart_fronts: BTreeMap<u8, NonNull<VerifierNode>>,
}

/// Localites in order of best to worst
fn locality_list() -> Vec<Locality> {
    vec![Locality::Thread, Locality::Global]
}

// `wfi` is less racy than instructions like `sw` or `lw` so we could treat it more precisely
// and allow a larger domain of possible programs. But for now, we treat it like `sw` or
// `lw` this means there exist some valid usecases that this will report as invalid, and
// for valid use cases it will be slower as it needs to explore and validate paths it
// doesn't need to theoritically do.
pub struct Explorerer {
    pub harts_range: Range<u8>,
    /// Program configurations that have been found to be invalid.
    pub excluded: BTreeSet<ProgramConfiguration>,
    /// Pointer to the 2nd element in the AST (e.g. it skips the 1st which is `.global _start`).
    pub second_ptr: NonNull<AstNode>,
    /// The different systems configurations to verify.
    pub roots: Vec<NonNull<VerifierConfiguration>>,
    // The current program configuration (e.g. variable types).
    pub configuration: ProgramConfiguration,
    // The queue of unexplored leaf nodes.
    pub queue: VecDeque<NonNull<VerifierLeafNode>>,
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
    pub unsafe fn new(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) -> Self {
        // You cannot verify a program that starts running on 0 harts.
        assert!(harts_range.start > 0);

        // Intial misc stuff
        let first = ast.unwrap().as_ref();
        let second_ptr = first.next.unwrap();
        let second = second_ptr.as_ref();
        match &first.this {
            Instruction::Global(Global { tag: start_tag }) => match &second.this {
                Instruction::Label(LabelInstruction { tag }) => {
                    assert_eq!(start_tag, tag);
                }
                _ => panic!("The second node must be the start label"),
            },
            _ => panic!("The first node must be the global start label definition"),
        }

        // To avoid retracing paths we record type combinations that have been found to be invalid.
        let excluded = BTreeSet::new();

        // The queue of nodes to explore along this path.
        // When we have 1..=3 harts the initial queue will contain
        // `[(_start, hart 0), (_start, hart 0), (_start, hart 0)]`
        // where each entry has a number of predeccessors e.g. `(_start, hart 1)`
        // up to the number of harts for that path.
        let roots = harts_range
            .clone()
            .map(|harts| {
                let ptr = alloc(Layout::new::<VerifierConfiguration>()).cast();
                ptr::write(
                    ptr,
                    VerifierConfiguration {
                        harts,
                        next: Vec::new(),
                    },
                );
                NonNull::new(ptr).unwrap()
            })
            .collect::<Vec<_>>();

        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let configuration = ProgramConfiguration::new();

        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let touched = BTreeSet::<NonNull<AstNode>>::new();

        // To remove uneeded branches we track the branches that actually jump.
        let jumped = BTreeSet::new();

        let queue = roots
            .iter()
            .enumerate()
            .map(|(harts, root)| {
                // All harts are intiailized as `_start`.
                let mut prev = PrevVerifierNode::Root(*root);
                let mut hart_fronts = BTreeMap::new();
                for hart in (0..=harts as u8).rev() {
                    let nonull = NonNull::new(Box::into_raw(Box::new(VerifierNode {
                        prev,
                        root: *root,
                        hart,
                        node: second_ptr,
                        next: Vec::new(),
                    })))
                    .unwrap();

                    prev.next().push(InnerNextVerifierNode::Branch(nonull));
                    prev = PrevVerifierNode::Branch(nonull);
                    hart_fronts.insert(hart, nonull);
                }
                let PrevVerifierNode::Branch(branch) = prev else {
                    unreachable!()
                };
                let leaf = NonNull::new(Box::into_raw(Box::new(VerifierLeafNode {
                    prev: branch,
                    variable_encounters: BTreeMap::new(),
                    hart_fronts,
                })))
                .unwrap();

                leaf
            })
            .collect::<VecDeque<_>>();

        Self {
            harts_range,
            roots,
            second_ptr,
            excluded,
            configuration,
            touched,
            queue,
            jumped,
            types: Default::default(),
            encountered: Default::default(),
        }
    }
    // Verify node before front leaf node, then queue new nodes.
    pub unsafe fn next_step(mut self) -> ExplorePathResult {
        trace!("excluded: {:?}", self.excluded);
        debug!("configuration: {:?}", self.configuration);

        let Some(leaf_ptr) = self.queue.front().copied() else {
            return ExplorePathResult::Valid(ValidPathResult {
                configuration: self.configuration.clone(),
                touched: self.touched.clone(),
                jumped: self.jumped.clone(),
            });
        };

        // If a variable is used that has not yet been defined, add the cheapest
        // possible data type for this variable to `types`. To avoid retreading the
        // steps of the same types, when the end of a invalid path is reached the
        // type map is added to `excluded`, we then check all values in `excluded`
        // and reduce the sets, e.g. (assuming the only data types are u8, u16 and u32)
        // if `[a:u8,b:u8]`, `[a:u8,b:u8]` and `[a:u8,b:u8]` are present in `excluded` then `[a:u8]` is added.
        let leaf = leaf_ptr.as_ref();
        let branch = leaf.prev.as_ref();
        let ast = branch.node;
        let hart = branch.hart;
        let root = branch.root.as_ref();
        let harts = root.harts;

        debug!(
            "current: {{ hart: {}/{}, instruction: \"{}\" }}",
            hart + 1,
            harts,
            branch.node.as_ref().span
        );

        // Record all the AST node that are reachable.
        self.touched.insert(ast);

        // Check the instruction is valid and make typing decisions.
        match &branch.node.as_ref().this {
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
            | Instruction::Beq(_) => {}
            Instruction::Define(Define {
                label,
                locality,
                cast,
            }) => {
                if !self.load_label(label, cast, locality, hart) {
                    return self.outer_invalid_path();
                }
            }
            Instruction::Lat(Lat { register: _, label }) => {
                if !self.load_label(label, None, None, hart) {
                    return self.outer_invalid_path();
                }
            }
            Instruction::La(La { register: _, label }) => {
                if !self.load_label(label, None, None, hart) {
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
                return self.outer_invalid_path();
            }
            x => todo!("{x:?}"),
        }
        self.queue_up(leaf_ptr);

        return ExplorePathResult::Continue(self);
    }

    pub unsafe fn outer_invalid_path(mut self) -> ExplorePathResult {
        // Deallocate node up to the 1st occurence of the most recently encountered variable.
        // If there is an invalid path without any variables defined, then there is no possible
        // valid path.
        // If the most recently encountered variable has exhausted all possible types, then move
        // on the the 2nd most recently encountered variable.
        while let Some(recent) = self.encountered.pop() {
            // Backtrace most recent variable encountered.
            self.invalid_path(&recent);

            // Are there any other possible types for this variable?
            let iter = self.types.get(&recent).unwrap();
            debug_assert_eq!(iter.size_hint().0, iter.size_hint().1.unwrap());
            if iter.size_hint().0 == 0 {
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
        // We need to track covered ground so we don't retread it.
        self.excluded.insert(self.configuration.clone());
        trace!("excluded: {:?}", self.excluded);

        // Remove from current type configuration.
        self.configuration.remove(recent);

        // Deallocate up to 1st occurence.
        let mut skip = BTreeSet::new();
        let mut new_queue = VecDeque::new();
        for leaf in &self.queue {
            if skip.contains(&leaf) {
                continue;
            }
            let Some(encounter) = leaf.as_ref().variable_encounters.get(&recent) else {
                continue;
            };
            let mut encounter_prev = *encounter.as_ref().prev.branch().unwrap();
            let mut variable_encounters = leaf.as_ref().variable_encounters.clone();

            // Deallocate all nodes including and after the encounter.
            let mut stack = vec![*encounter];
            while let Some(current) = stack.pop() {
                match &current.as_ref().next {
                    InnerNextVerifierNode::Branch(branches) => {
                        for b in branches {
                            stack.push(*b);
                        }
                    }
                    InnerNextVerifierNode::Leaf(l) => {
                        skip.insert(l);
                        debug_assert_eq!(
                            l.as_ref().variable_encounters.get(&recent).unwrap(),
                            encounter
                        );
                        dealloc(leaf.as_ptr().cast(), Layout::new::<VerifierLeafNode>());
                    }
                }
                // If a variable is present in this instruction.
                if let Some(var) = current.as_ref().node.as_ref().this.variable() {
                    // If this node is the 1st where the variable is encountered.
                    if current == *variable_encounters.get(var).unwrap() {
                        variable_encounters.remove(var);
                    }
                }
                // If the cached state belongs to any of the nodes being deallocated it must be discarded.
                if let Some(cs) = &cached_state {
                    if cs.1 == current {
                        cached_state = None;
                    }
                }
                dealloc(current.as_ptr().cast(), Layout::new::<VerifierNode>());
            }

            // Set the new leaf node.
            //
            // We could do this more efficiently by storing `hart_prev` on `VerifierNode` to indicate the last node on
            // the same hart. Unfortunately since we will have a large number of `VerifierNode`s this will add a massive
            // amount to memory usage for (what I estimate to be) a relatively insignficant runtime improvement.
            // TODO produce a comparison using the `hart_prev` approach.
            let mut hart_fronts = BTreeMap::new();
            let mut start = encounter_prev;
            while hart_fronts.len() < leaf.as_ref().hart_fronts.len() {
                if !hart_fronts.contains_key(&start.as_ref().hart) {
                    hart_fronts.insert(start.as_ref().hart, start);
                }
                start = *start.as_ref().prev.branch().unwrap();
            }

            // Set the new leaf.
            let new_leaf = NonNull::new(Box::into_raw(Box::new(VerifierLeafNode {
                prev: encounter_prev,
                variable_encounters,
                hart_fronts,
            })))
            .unwrap();
            encounter_prev.as_mut().next = InnerNextVerifierNode::Leaf(new_leaf);
            new_queue.push_back(new_leaf);
        }
        // Set new queue.
        self.queue = new_queue;
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
        label: &Label,
        ttype: impl Borrow<Option<Type>>, // The type to use for the variable if `Some(_)`.
        locality: impl Borrow<Option<Locality>>, // The locality to use for the variable if `Some(_)`.
        hart: u8,
    ) -> bool {
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

        // Get the iterator yielding the next type for `label` or if this is the 1st encounter adds the new iterator for types.
        let iter = self.types.entry(label.clone()).or_insert_with(|| {
            debug_assert!(self.encountered.iter().find(|l| *l == label).is_none());
            self.encountered.push(label.clone());
            Box::new(locality_list().into_iter().cartesian_product(type_list()))
        });
        // This looks how it does since the example code is valid (assuming x is known at compile-time) and it needs to support this:
        // ```
        // if typeof x = u8
        //   define y _ u8
        // if typeof x = i8
        //   define y _ i8
        // ```
        while let Some((possible_locality, possible_type)) = iter.next() {
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

            let mut config = self.configuration.clone();
            config.insert(label.clone(), hart, (possible_locality, possible_type));

            // Check not excluded.
            if self.excluded.contains(&config) {
                continue;
            }

            // Found valid typing.
            self.configuration = config;
            return true;
        }
        return false;
    }

    unsafe fn check_store(
        mut self,
        leaf_ptr: NonNull<VerifierLeafNode>,
        branch: &VerifierNode,
        to: &Register,
        offset: &crate::ast::Offset,
        type_size: u64,
    ) -> Result<Self, ExplorePathResult> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration);

        // Check the destination is valid.
        match state.registers[branch.hart as usize].get(to) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) = state.configuration.get(from_label.into()).unwrap();
                // If attempting to access outside the memory space for the label.
                let full_offset = MemoryValueU64::from(type_size)
                    .add(from_offset)
                    .unwrap()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.value.value).unwrap(),
                    ))
                    .unwrap();
                let size = size(ttype);

                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
                        return Err(self.outer_invalid_path());
                    }
                    true => {
                        // Else we found the label and we can validate that the loading
                        // of a word with the given offset is within the address space.
                        // So we continue exploration.
                        Ok(self)
                    }
                }
            }
            x => todo!("{x:?}"),
        }
    }

    /// Verifies a load is valid for a given configuration.
    unsafe fn check_load(
        mut self,
        leaf_ptr: NonNull<VerifierLeafNode>,
        branch: &VerifierNode,
        from: &Register,
        offset: &crate::ast::Offset,
        type_size: u64,
    ) -> Result<Self, ExplorePathResult> {
        // Collect the state.
        let state = find_state(leaf_ptr, &self.configuration);

        // Check the destination is valid.
        match state.registers[branch.hart as usize].get(from) {
            Some(MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr {
                tag: from_label,
                offset: from_offset,
            })))) => {
                let (_locality, ttype) = state.configuration.get(from_label.into()).unwrap();

                // If attempting to access outside the memory space for the label.
                let full_offset = MemoryValueU64::from(type_size)
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.value.value).unwrap(),
                    ))
                    .unwrap()
                    .add(from_offset)
                    .unwrap();
                let size = size(ttype);
                match full_offset.lte(&size) {
                    false => {
                        // The path is invalid, so we add the current types to the
                        // excluded list and restart exploration.
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
    unsafe fn queue_up(&mut self, mut leaf_ptr: NonNull<VerifierLeafNode>) {
        let queue = &mut self.queue;
        let configuration = &mut self.configuration;
        let jumped = &mut self.jumped;
        // TOOD We duplicate so much work doing `find_state` in a bunch of places and
        // multiple times when the state hasn't change, we should avoid doing this call
        // here (and remove the it in other places).
        let state = find_state(leaf_ptr, configuration);
        let leaf = leaf_ptr.as_mut();

        // Search the verifier tree for the fronts of all harts.
        let mut fronts = BTreeMap::new();
        let mut current = leaf.prev.as_ref();
        let harts = current.root.as_ref().harts;
        fronts.insert(current.hart, current.node);
        while fronts.len() < harts as usize {
            let PrevVerifierNode::Branch(branch) = current.prev else {
                unreachable!()
            };
            current = branch.as_ref();
            fronts.entry(current.hart).or_insert(current.node);
        }

        trace!(
            "fronts: {:?}",
            fronts
                .iter()
                .map(|(hart, ast)| (hart, ast.as_ref().this.to_string()))
                .collect::<BTreeMap<_, _>>()
        );

        let followup = |node: NonNull<AstNode>,
                        hart: u8|
         -> Option<Result<(u8, NonNull<AstNode>), (u8, NonNull<AstNode>)>> {
            match &node.as_ref().this {
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
                | Instruction::Beq(_) => Some(Err((hart, node))),
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
                        x => todo!("{x:?}"),
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
                match &node_ref.this {
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
                                followup(label_node, hart)
                            }
                            Some(RangeOrdering::Equal) => followup(node_ref.next.unwrap(), hart),
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

        debug!("racy: {}", next_nodes.is_ok());

        debug!(
            "next: {:?}",
            next_nodes
                .as_ref()
                .map(|racy| racy
                    .iter()
                    .map(|(h, n)| format!(
                        "{{ hart: {h}, instruction: {} }}",
                        n.as_ref().this.to_string()
                    ))
                    .collect::<Vec<_>>())
                .map_err(|(h, n)| format!(
                    "{{ hart: {h}, instruction: {} }}",
                    n.as_ref().this.to_string()
                ))
        );
        match next_nodes {
            // If there was a non-racy node, enqueue this single node.
            Err((hart, non_racy_next)) => {
                let mut branch_ptr = leaf.prev;
                let branch = branch_ptr.as_mut();
                let new_branch = NonNull::new(Box::into_raw(Box::new(VerifierNode {
                    prev: PrevVerifierNode::Branch(branch_ptr),
                    root: branch.root,
                    hart,
                    node: non_racy_next,
                    next: InnerNextVerifierNode::Leaf(leaf_ptr)
                }))).unwrap();
                leaf.prev = new_branch;
                branch.next = InnerNextVerifierNode::Branch(vec![new_branch]);

                queue.push_back(leaf_ptr);
            }
            // If all nodes where racy, enqueue these nodes.
            Ok(racy_nodes) => {
                let mut branch_ptr = leaf.prev;
                let branch = branch_ptr.as_mut();

                let new_branches = racy_nodes.iter().copied().map(|(hart, node)| {
                    
                    let new_branch = NonNull::new(Box::into_raw(Box::new(VerifierNode {
                        prev: PrevVerifierNode::Branch(branch_ptr),
                        root: branch.root,
                        hart,
                        node,
                        next: InnerNextVerifierNode::Leaf(NonNull::new_unchecked(std::ptr::null_mut()))
                    }))).unwrap();
                    let new_leaf = NonNull::new(Box::into_raw(Box::new(VerifierLeafNode {
                        prev: new_branch,
                    })));

                    new_branch
                }).collect();
                
                branch.next = InnerNextVerifierNode::Branch(new_branches)
            }
        }
    }
}

use itertools::Itertools;
use std::borrow::Borrow;

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
    pub configuration: ProgramConfiguration,
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
unsafe fn get_backpath_harts(prev: NonNull<VerifierLeafNode>) -> Vec<usize> {
    let mut current = prev.as_ref().prev;
    let mut record = Vec::new();
    while let PrevVerifierNode::Branch(branch) = current.as_ref().prev {
        let r = match &branch.as_ref().next {
            InnerNextVerifierNode::Branch(branches) => {
                branches.iter().position(|&x| x == current).unwrap()
            }
            InnerNextVerifierNode::Leaf(_) => unreachable!(),
        };
        record.push(r);
        current = branch
    }
    let PrevVerifierNode::Root(root) = current.as_ref().prev else {
        unreachable!()
    };
    record
}

/// Creates a new verifier node from an AST node at the edge of a branch.
unsafe fn simple_nonnull(
    mut leaf: NonNull<VerifierLeafNode>,
    node: NonNull<AstNode>,
    hart: u8,
) -> NonNull<VerifierNode> {
    let mut leaf_ref = leaf.as_ref();
    let mut branch_ref = leaf_ref.prev.as_ref();
    let new = NonNull::new(Box::into_raw(Box::new(VerifierNode {
        prev: PrevVerifierNode::Branch(leaf_ref.prev),
        root: branch_ref.root,
        hart,
        node,
        next: InnerNextVerifierNode::Leaf(leaf)
    }))).unwrap();
    leaf_ref.prev = new;
    branch_ref.next = InnerNextVerifierNode::Branch(vec![new]);
    
    let ptr = alloc(Layout::new::<VerifierNode>()).cast();
    ptr::write(
        ptr,
        VerifierNode {
            prev: PrevVerifierNode::Branch(prev),
            hart,
            node,
            next: Vec::new(),
        },
    );
    let nonull = NonNull::new(ptr).unwrap();
    prev.as_mut().next.push(nonull);
    nonull
}

unsafe fn find_label(node: NonNull<AstNode>, label: &Label) -> Option<NonNull<AstNode>> {
    // Check start
    if let Instruction::Label(LabelInstruction { tag }) = &node.as_ref().this {
        if tag == label {
            return Some(node);
        }
    }

    // Trace backwards.
    let mut back = node;
    while let Some(prev) = back.as_ref().prev {
        if let Instruction::Label(LabelInstruction { tag }) = &prev.as_ref().this {
            if tag == label {
                return Some(prev);
            }
        }
        back = prev;
    }

    // Trace forward.
    let mut front = node;
    while let Some(next) = front.as_ref().next {
        if let Instruction::Label(LabelInstruction { tag }) = &next.as_ref().this {
            if tag == label {
                return Some(next);
            }
        }
        front = next;
    }

    None
}

unsafe fn find_state(
    leaf: NonNull<VerifierLeafNode>, // The record of which children to follow from the root to reach the current position.
    configuration: &ProgramConfiguration,
) -> State {
    let record = get_backpath_harts(leaf);
    let root = leaf.as_ref().prev.as_ref().root;
    let harts = root.as_ref().harts;

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
    let mut state = State::new(harts, configuration);
    let mut current = root.as_ref().next;
    for next in record.iter().rev() {
        let vnode = current.as_ref();
        let hart = vnode.hart;
        let hartu = hart as usize;
        match &vnode.node.as_ref().this {
            // Instructions with no side affects.
            Instruction::Label(_)
            | Instruction::Blt(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_)
            | Instruction::Bne(_)
            | Instruction::Branch(_)
            | Instruction::Beq(_) => {}
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
        current = match &current.as_ref().next {
            InnerNextVerifierNode::Branch(b) => b[*next],
            InnerNextVerifierNode::Leaf(_) => unreachable!(),
        };
    }
    state
}

fn find_state_store(
    state: &mut State,
    hartu: usize,
    to: &Register,
    from: &Register,
    offset: &Offset,
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
            let (locality, to_type) = state.configuration.get(to_label.into()).unwrap();
            // We should have already checked the type is large enough for the store.
            let sizeof = size(to_type);
            let final_offset = MemoryValueU64::from(len)
                .add(to_offset)
                .unwrap()
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.value.value).unwrap(),
                ))
                .unwrap();
            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(to_label));
            let memloc = MemoryPtr(Some(NonNullMemoryPtr {
                tag: to_label.clone(),
                offset: to_offset
                    .clone()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.value.value).unwrap(),
                    ))
                    .unwrap(),
            }));
            state.memory.set(&memloc, &len, from_value.clone()).unwrap();
        }
        _ => todo!(),
    }
}

fn find_state_load(
    state: &mut State,
    hartu: usize,
    to: &Register,
    from: &Register,
    offset: &Offset,
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
            let (locality, from_type) = state.configuration.get(from_label.into()).unwrap();
            // We should have already checked the type is large enough for the load.
            let sizeof = size(from_type);
            let final_offset = MemoryValueU64::from(len)
                .add(from_offset)
                .unwrap()
                .add(&MemoryValueU64::from(
                    u64::try_from(offset.value.value).unwrap(),
                ))
                .unwrap();

            debug_assert!(final_offset.lte(&sizeof));
            debug_assert_eq!(locality, <&Locality>::from(from_label));

            let memloc = Slice {
                base: from_label.clone(),
                offset: from_offset
                    .clone()
                    .add(&MemoryValueU64::from(
                        u64::try_from(offset.value.value).unwrap(),
                    ))
                    .unwrap(),
                len,
            };
            let value = state.memory.get(&memloc).unwrap();
            state.registers[hartu].insert(*to, value).unwrap();
        }
        x => todo!("{x:?}"),
    }
}
