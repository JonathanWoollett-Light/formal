use crate::ast::*;
use crate::verifier_types::*;
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
pub struct VerifierHarts {
    pub harts: u8,
    pub next: NextVerifierNode,
}

type NextVerifierNode = Vec<NonNull<VerifierNode>>;

#[derive(Debug, Clone, Copy)]
enum VerifierPrevNode {
    Branch(NonNull<VerifierNode>),
    Root(NonNull<VerifierHarts>),
}

impl VerifierPrevNode {
    unsafe fn next(&mut self) -> &mut NextVerifierNode {
        match self {
            VerifierPrevNode::Branch(branch) => &mut branch.as_mut().next,
            VerifierPrevNode::Root(root) => &mut root.as_mut().next,
        }
    }
}

/// We use a tree to trace the execution of the program,
/// then when conditions are required it can resolve them
/// by looking back at the trace.
pub struct VerifierNode {
    pub prev: VerifierPrevNode,
    pub hart: u8,
    pub node: NonNull<AstNode>,
    pub next: NextVerifierNode,
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
#[derive(Debug)]
pub struct Explorerer {
    pub harts_range: Range<u8>,
    pub excluded: BTreeSet<ProgramConfiguration>,
    /// Pointer to the 2nd element in the AST (e.g. it skips the 1st which is `.global _start`).
    pub second_ptr: NonNull<AstNode>,
    pub roots: Vec<NonNull<VerifierHarts>>,
}

impl Explorerer {
    pub unsafe fn new_path(this: Rc<RefCell<Self>>) -> ExplorererPath {
        let this_ref = this.borrow_mut();
        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let configuration = ProgramConfiguration::new();

        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let touched = BTreeSet::<NonNull<AstNode>>::new();

        // To remove uneeded branches we track the branches that actually jump.
        let jumped = BTreeSet::new();

        let queue = this_ref
            .roots
            .iter()
            .enumerate()
            .map(|(harts, root)| {
                // All harts are intiailized as `_start`.
                let mut prev = VerifierPrevNode::Root(*root);
                for hart in (0..=harts as u8).rev() {
                    let nonull = {
                        let ptr = alloc(Layout::new::<VerifierNode>()).cast();
                        ptr::write(
                            ptr,
                            VerifierNode {
                                prev,
                                hart,
                                node: this_ref.second_ptr,
                                next: Vec::new(),
                            },
                        );
                        NonNull::new(ptr).unwrap()
                    };

                    prev.next().push(nonull);
                    prev = VerifierPrevNode::Branch(nonull);
                }
                let VerifierPrevNode::Branch(branch) = prev else {
                    unreachable!()
                };
                branch
            })
            .collect::<VecDeque<_>>();
        drop(this_ref);

        ExplorererPath {
            explorerer: this,
            configuration,
            touched,
            queue,
            jumped,
        }
    }

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
                let ptr = alloc(Layout::new::<VerifierHarts>()).cast();
                ptr::write(
                    ptr,
                    VerifierHarts {
                        harts,
                        next: Vec::new(),
                    },
                );
                NonNull::new(ptr).unwrap()
            })
            .collect::<Vec<_>>();

        Self {
            harts_range,
            roots,
            second_ptr,
            excluded,
        }
    }
}

/// Represents a set of assumptions that lead to a given execution path (e.g. intial types of variables before they are explictly cast).
#[derive(Debug)]
pub struct ExplorererPath {
    // This could be a mutable reference. Its a `Rc<RefCell<_>>` becuase the borrow checker can't
    // figure out its safe and I don't want to rework the code right now to help it.
    pub explorerer: Rc<RefCell<Explorerer>>,

    pub configuration: ProgramConfiguration,
    // All the nodes that are touched.
    pub touched: BTreeSet<NonNull<AstNode>>,
    pub queue: VecDeque<NonNull<VerifierNode>>,
    // All the branch nodes that jump.
    pub jumped: BTreeSet<NonNull<AstNode>>,
}

/// Attempts to modify initial types to include a new variable, if it cannot add it,
/// existing is added to excluded, then returns true.
///
/// # Returns
///
/// - `true` the path is valid.
/// - `false` the path is invalid.
fn load_label(
    label: &Label,
    configuration: &mut ProgramConfiguration,
    excluded: &mut BTreeSet<ProgramConfiguration>,
    ttype: Option<Type>,        // The type to use for the variable if `Some(_)`.
    locality: Option<Locality>, // The locality to use for the variable if `Some(_)`.
    hart: u8,
) -> bool {
    // If the variable is already define, the type and locality must match any given.
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
    if let Some((existing_locality, existing_type)) = configuration.get(label) {
        if let Some(given_type) = ttype {
            if given_type != *existing_type {
                return false;
            }
        }
        if let Some(given_locality) = locality {
            if given_locality != *existing_locality {
                return false;
            }
        }
        return true;
    }

    // If a locality is given restrict exploration to this locality.
    let liter = match locality {
        Some(given) => vec![given],
        None => locality_list(),
    };
    // If a type is given restrict exploration to this type.
    let titer = match ttype {
        Some(given) => vec![given],
        None => type_list(),
    };

    // Search for a type and locality it can be that hasn't yet been excluded.
    for locality in liter {
        for ttype in titer.iter().cloned() {
            let mut config = configuration.clone();
            config.insert(label.clone(), hart, (locality, ttype));

            if !excluded.contains(&config) {
                *configuration = config;
                return true;
            }
        }
    }
    false
}

#[derive(Debug)]
pub enum ExplorePathResult {
    Valid(ValidPathResult),
    Invalid(InvalidPathResult),
    Continue(ExplorererPath),
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
impl ExplorePathResult {
    pub fn continued(self) -> Option<ExplorererPath> {
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
    pub fn invalid(self) -> Option<InvalidPathResult> {
        match self {
            Self::Invalid(c) => Some(c),
            _ => None,
        }
    }
}

use itertools::intersperse;
use tracing::debug;
impl ExplorererPath {
    pub unsafe fn next_step(
        Self {
            explorerer,
            mut configuration,
            mut touched,
            mut queue,
            mut jumped,
        }: Self,
    ) -> ExplorePathResult {
        trace!("excluded: {:?}", explorerer.borrow().excluded);
        debug!("configuration: {configuration:?}");

        debug!(
            "queue: [{}]",
            intersperse(
                queue.iter().map(|item| {
                    let mut current = item.as_ref().prev;
                    while let VerifierPrevNode::Branch(prev) = current {
                        current = prev.as_ref().prev;
                    }
                    let VerifierPrevNode::Root(root) = current else {
                        unreachable!()
                    };

                    let item_ref = item.as_ref();
                    format!(
                        "{{ hart: {}/{}, instruction: \"{}\" }}",
                        item_ref.hart + 1,
                        root.as_ref().harts,
                        item_ref.node.as_ref().span
                    )
                }),
                String::from(", ")
            )
            .collect::<String>()
        );

        let Some(branch_ptr) = queue.pop_front() else {
            return ExplorePathResult::Valid(ValidPathResult {
                configuration,
                touched,
                jumped,
            });
        };

        // If a variable is used that has not yet been defined, add the cheapest
        // possible data type for this variable to `types`. To avoid retreading the
        // steps of the same types, when the end of a invalid path is reached the
        // type map is added to `excluded`, we then check all values in `excluded`
        // and reduce the sets, e.g. (assuming the only data types are u8, u16 and u32)
        // if `[a:u8,b:u8]`, `[a:u8,b:u8]` and `[a:u8,b:u8]` are present in `excluded` then `[a:u8]` is added.
        let branch = branch_ptr.as_ref();
        let ast = branch.node;
        let hart = branch.hart;

        let mut current = branch_ptr.as_ref().prev;
        while let VerifierPrevNode::Branch(prev) = current {
            current = prev.as_ref().prev;
        }
        let VerifierPrevNode::Root(root) = current else {
            unreachable!()
        };
        let harts = root.as_ref().harts;
        debug!(
            "current: {{ hart: {}/{}, instruction: \"{}\" }}",
            hart + 1,
            harts,
            branch_ptr.as_ref().node.as_ref().span
        );

        // Record all the AST node that are reachable.
        touched.insert(ast);

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
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.borrow_mut().excluded,
                    cast.clone(),
                    *locality,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
                        configuration,
                        harts,
                        InvalidExplanation::La(label.clone()),
                    );
                }
            }
            Instruction::Lat(Lat { register: _, label }) => {
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.borrow_mut().excluded,
                    None,
                    None,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
                        configuration,
                        harts,
                        InvalidExplanation::Lat(label.clone()),
                    );
                }
            }
            Instruction::La(La { register: _, label }) => {
                if !load_label(
                    label,
                    &mut configuration,
                    &mut explorerer.borrow_mut().excluded,
                    None,
                    None,
                    hart,
                ) {
                    return invalid_path(
                        explorerer.clone(),
                        configuration,
                        harts,
                        InvalidExplanation::La(label.clone()),
                    );
                }
            }
            // For any store we need to validate the destination is valid.
            Instruction::Sw(Sw {
                to,
                from: _,
                offset,
            }) => {
                if let Some(res) = check_store(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    to,
                    offset,
                    4,
                    InvalidExplanation::Sw,
                ) {
                    return res;
                }
            }
            Instruction::Sb(Sb {
                to,
                from: _,
                offset,
            }) => {
                if let Some(res) = check_store(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    to,
                    offset,
                    1,
                    InvalidExplanation::Sb,
                ) {
                    return res;
                }
            }
            // TODO A lot of the checking loads code is duplicated, reduce this duplication.
            // For any load we need to validate the destination is valid.
            Instruction::Ld(Ld {
                to: _,
                from,
                offset,
            }) => {
                if let Some(res) = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    8,
                    InvalidExplanation::Ld,
                ) {
                    return res;
                }
            }
            Instruction::Lw(Lw {
                to: _,
                from,
                offset,
            }) => {
                if let Some(res) = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    4,
                    InvalidExplanation::Lw,
                ) {
                    return res;
                }
            }
            Instruction::Lb(Lb {
                to: _,
                from,
                offset,
            }) => {
                let opt = check_load(
                    explorerer.clone(),
                    branch_ptr,
                    branch,
                    &configuration,
                    from,
                    offset,
                    1,
                    InvalidExplanation::Lb,
                );
                if let Some(res) = opt {
                    return res;
                }
            }
            // If any fail is encountered then the path is invalid.
            Instruction::Fail(_) => {
                return invalid_path(
                    explorerer.clone(),
                    configuration,
                    harts,
                    InvalidExplanation::Fail,
                )
            }
            x => todo!("{x:?}"),
        }
        queue_up(branch_ptr, &mut queue, &configuration, &mut jumped);

        return ExplorePathResult::Continue(Self {
            explorerer,
            configuration,
            touched,
            queue,
            jumped,
        });
    }
}

unsafe fn check_store(
    explorerer: Rc<RefCell<Explorerer>>,
    branch_ptr: NonNull<VerifierNode>,
    branch: &VerifierNode,
    configuration: &ProgramConfiguration,
    to: &Register,
    offset: &crate::ast::Offset,
    type_size: u64,
    invalid: InvalidExplanation,
) -> Option<ExplorePathResult> {
    // Collect the state.
    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
    let state = find_state(&record, root, harts, first_step, &configuration);

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
                    return Some(invalid_path(
                        explorerer.clone(),
                        configuration.clone(),
                        harts,
                        invalid,
                    ));
                }
                true => {
                    // Else we found the label and we can validate that the loading
                    // of a word with the given offset is within the address space.
                    // So we continue exploration.
                    None
                }
            }
        }
        x => todo!("{x:?}"),
    }
}

/// Verifies a load is valid for a given configuration.
unsafe fn check_load(
    explorerer: Rc<RefCell<Explorerer>>,
    branch_ptr: NonNull<VerifierNode>,
    branch: &VerifierNode,
    configuration: &ProgramConfiguration,
    from: &Register,
    offset: &crate::ast::Offset,
    type_size: u64,
    invalid: InvalidExplanation,
) -> Option<ExplorePathResult> {
    // Collect the state.
    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
    let state = find_state(&record, root, harts, first_step, &configuration);

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
                    return Some(invalid_path(
                        explorerer.clone(),
                        configuration.clone(),
                        harts,
                        invalid,
                    ));
                }
                true => {
                    // Else, we found the label and we can validate that the loading
                    // of a word with the given offset is within the address space.
                    // So we continue exploration.
                    None
                }
            }
        }
        x => todo!("{x:?}"),
    }
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

unsafe fn invalid_path(
    explorerer: Rc<RefCell<Explorerer>>,
    configuration: ProgramConfiguration,
    harts: u8,
    explanation: InvalidExplanation,
) -> ExplorePathResult {
    let mut explorer_ref = explorerer.borrow_mut();
    // We need to track covered ground so we don't retread it.
    explorer_ref.excluded.insert(configuration.clone());

    trace!("excluded: {:?}", explorer_ref.excluded);

    let harts_root = explorer_ref
        .roots
        .iter()
        .find(|root| root.as_ref().harts == harts)
        .unwrap();
    let [hart_root] = harts_root.as_ref().next.as_slice() else {
        unreachable!()
    };
    let path = crate::draw::draw_tree(*hart_root, 2, |n| {
        let r = n.as_ref();
        format!("{}, {}", r.hart + 1, r.node.as_ref().this)
    });

    // Dealloc the current tree so we can restart.
    for mut root in explorer_ref.roots.iter().copied() {
        let stack = &mut root.as_mut().next;
        while let Some(next) = stack.pop() {
            stack.extend(next.as_ref().next.iter());
            dealloc(next.as_ptr().cast(), Layout::new::<VerifierNode>());
        }
    }

    // TODO Make this path better and doublecheck if this is actually correct behaviour.
    // This case only occurs when all types are excluded thus it continually breaks out
    // of the exploration loop with empty `initial_types`. This case means there is no
    // valid type combination and thus no valid path.
    ExplorePathResult::Invalid(InvalidPathResult {
        complete: configuration.0.is_empty(),
        path,
        explanation,
    })
}

// Get the number of harts of this sub-tree and record the path.
unsafe fn get_backpath_harts(
    prev: NonNull<VerifierNode>,
) -> (Vec<usize>, NonNull<VerifierHarts>, u8, usize) {
    let mut current = prev;
    let mut record = Vec::new();
    while let VerifierPrevNode::Branch(branch) = current.as_ref().prev {
        let r = branch
            .as_ref()
            .next
            .iter()
            .position(|&x| x == current)
            .unwrap();
        record.push(r);
        current = branch
    }
    let VerifierPrevNode::Root(root) = current.as_ref().prev else {
        unreachable!()
    };
    let harts = root.as_ref().harts;
    let first_step = root
        .as_ref()
        .next
        .iter()
        .position(|&x| x == current)
        .unwrap();
    (record, root, harts, first_step)
}

/// Queues up the next node to evaluate.
///
/// We look at the next node for the 1st hart and queue this up if its not racy,
/// if its racy, we look at the 2nd hart and queue it up if its not racy,
/// if its racy we look at the 3rd hart etc. If all next nodes are racy, we queue
/// up all racy instructions (since we need to evaluate all the possible ordering of them).

unsafe fn queue_up(
    prev: NonNull<VerifierNode>,
    queue: &mut VecDeque<NonNull<VerifierNode>>,
    configuration: &ProgramConfiguration,
    jumped: &mut BTreeSet<NonNull<AstNode>>,
) {
    let (record, root, harts, first_step) = get_backpath_harts(prev);
    // TOOD We duplicate so much work doing `find_state` in a bunch of places and
    // multiple times when the state hasn't change, we should avoid doing this call
    // here (and remove the it in other places).
    let state = find_state(&record, root, harts, first_step, configuration);

    // Search the verifier tree for the fronts of all harts.
    let mut fronts = BTreeMap::new();
    let mut current = prev.as_ref();
    fronts.insert(current.hart, current.node);
    while fronts.len() < harts as usize {
        let VerifierPrevNode::Branch(branch) = current.prev else {
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
                if let MemoryValue::Ptr(MemoryPtr(Some(NonNullMemoryPtr { tag, offset: _ }))) =
                    value
                {
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
                } else {
                    todo!()
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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
                    let state = find_state(&record, root, harts, first_step, configuration);

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
            queue.push_back(simple_nonnull(prev, non_racy_next, hart));
        }
        // If all nodes where racy, enqueue these nodes.
        Ok(racy_nodes) => {
            for (hart, node) in racy_nodes {
                queue.push_back(simple_nonnull(prev, node, hart));
            }
        }
    }
}

unsafe fn simple_nonnull(
    mut prev: NonNull<VerifierNode>,
    node: NonNull<AstNode>,
    hart: u8,
) -> NonNull<VerifierNode> {
    let ptr = alloc(Layout::new::<VerifierNode>()).cast();
    ptr::write(
        ptr,
        VerifierNode {
            prev: VerifierPrevNode::Branch(prev),
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
    record: &[usize], // The record of which children to follow from the root to reach the current position.
    root: NonNull<VerifierHarts>, // The root of the verification tree.
    harts: u8,        // The number of hardware threads in the current path.
    first_step: usize, // The child node of the root which forms the current path (will correlate with `harts`).
    configuration: &ProgramConfiguration,
) -> State {
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
    let mut current = root.as_ref().next[first_step];
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
        current = current.as_ref().next[*next];
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
