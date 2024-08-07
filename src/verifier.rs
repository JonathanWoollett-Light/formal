use crate::ast::*;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::hash::Hash;
use std::iter;
use std::num::NonZeroU8;
use std::ops::Range;
use std::ops::RangeInclusive;
use std::ptr;
use std::{
    alloc::alloc,
    collections::{HashMap, VecDeque},
    ptr::NonNull,
};

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
enum Type {
    U8,
    I8,
    U16,
    I16,
    U32,
    I32,
    U64,
    I64,
    List(Vec<Type>),
}

fn size(t: &Type) -> usize {
    use Type::*;
    match t {
        U8 => 1,
        I8 => 1,
        U16 => 2,
        I16 => 2,
        U32 => 4,
        I32 => 4,
        U64 => 8,
        I64 => 8,
        _ => todo!(),
    }
}

const TYPE_LIST: [Type; 8] = [
    Type::U8,
    Type::I8,
    Type::U16,
    Type::I16,
    Type::U32,
    Type::I32,
    Type::U64,
    Type::I64,
];

struct VerifierHarts {
    harts: u8,
    next: NextVerifierNode,
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

type Types = BTreeMap<Label, Type>;
type Excluded = HashSet<BTreeMap<Label, Type>>;


#[derive(Debug)]
struct MemoryMap {
    map: HashMap<Label, MemoryValue>
}

impl MemoryMap {
    fn get_byte(&self, MemoryLocation{ label, offset}: &MemoryLocation) -> Option<&u8> {
        let value = self.map.get(label)?;
        match value {
            MemoryValue::Ascii(ascii) => ascii.get(*offset),
            MemoryValue::Word(word) => word.get(*offset),
            _ => todo!()
        }
    }
    fn get_word(&self, MemoryLocation{ label, offset}: &MemoryLocation) -> Option<&[u8;4]> {
        let value = self.map.get(label)?;
        match value {
            MemoryValue::Word(word) => (*offset == 0).then_some(word),
            _ => todo!()
        }
    }
    fn set_word(&mut self, MemoryLocation{ label, offset}: &MemoryLocation, value: [u8;4]) {
        if let Some(existing) = self.map.get_mut(label) {
            match existing {
                MemoryValue::Word(word) => {
                    *word = value;
                }
                _ => todo!()
            }
        }
        else {
            if *offset == 0 {
                self.map.insert(label.clone(), MemoryValue::Word(value));
            }
            else {
                todo!()
            }
            
        }
    }
}

#[derive(Debug)]
struct State {
    registers: Vec<HashMap<Register, RegisterValue>>,
    memory: MemoryMap,
}
impl State {
    fn new(harts: u8) -> Self {
        Self {
            registers: (0..harts).map(|_| HashMap::new()).collect(),
            memory: MemoryMap { map: HashMap::new() },
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash)]
#[non_exhaustive]
struct MemoryLocation {
    label: Label,
    offset: usize
}

impl From<Label> for MemoryLocation {
    fn from(label: Label) -> MemoryLocation {
        MemoryLocation {
            label,
            offset: 0
        }
    }
}
impl From<&Label> for MemoryLocation {
    fn from(label: &Label) -> MemoryLocation {
        MemoryLocation {
            label: label.clone(),
            offset: 0
        }
    }
}

// It is possible to technically store a 4 byte virtual value (e.g. DATA_END)
// then edit 2 bytes of it. So we will need additional complexity to support this case
#[derive(Debug)]
#[non_exhaustive]
enum MemoryValue {
    Word([u8; 4]),
    Ascii(Vec<u8>)
}

#[derive(Debug, Clone)]
#[non_exhaustive]
enum RegisterValue {
    Immediate(ImmediateRange),
    Address(Label),
    Csr(CsrValue),
}
impl From<Immediate> for RegisterValue {
    fn from(imm: Immediate) -> Self {
        Self::Immediate(ImmediateRange(imm..=imm))
    }
}
impl From<Label> for RegisterValue {
    fn from(label: Label) -> Self {
        Self::Address(label)
    }
}

#[derive(Debug, Clone)]
#[non_exhaustive]
enum CsrValue {
    Mhartid,
}

#[derive(Debug, Clone)]
struct ImmediateRange(RangeInclusive<Immediate>);
impl ImmediateRange {
    pub fn value(&self) -> Option<Immediate> {
        if self.0.start() == self.0.end() {
            Some(*self.0.start())
        } else {
            None
        }
    }
}
impl std::ops::Add for ImmediateRange {
    type Output = Self;

    fn add(self, other: Self) -> Self {
        Self(*self.0.start() + *other.0.start()..=*self.0.end() + *other.0.end())
    }
}
impl std::ops::Add<Immediate> for ImmediateRange {
    type Output = Self;

    fn add(self, other: Immediate) -> Self {
        Self(*self.0.start() + other..=*self.0.end() + other)
    }
}

// `wfi` is less racy than instructions like `sw` or `lw` so we could treat it more precisely
// and allow a larger domain of possible programs. But for now, we treat it like `sw` or
// `lw` this means there exist some valid usecases that this will report as invalid, and
// for valid use cases it will be slower as it needs to explore and validate paths it
// doesn't need to theoritically do.

pub unsafe fn verify(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) {
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

    // Record the types of variables we have previously found form invalid paths.
    let mut excluded = Excluded::new();

    // The queue of nodes to explore along this path.
    // When we have 1..=3 harts the initial queue will contain
    // `[(_start, hart 0), (_start, hart 0), (_start, hart 0)]`
    // where each entry has a number of predeccessors e.g. `(_start, hart 1)`
    // up to the number of harts for that path.
    let roots = harts_range
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

    #[cfg(debug_assertions)]
    let mut check = 0;
    let (final_types, final_touched) = loop {
        // Record the current types of variables on the current path.
        let mut types = Types::new();
        // To remove uneeded code (e.g. a branch might always be true so we remove the code it skips)
        // we record all the AST instructions that get touched.
        let mut touched = HashSet::<NonNull<AstNode>>::new();

        let mut queue = roots
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
                                node: second_ptr,
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

        'outer: while let Some(branch_ptr) = queue.pop_front() {
            // If a variable is used that has not yet been defined, add the cheapest
            // possible data type for this variable to `types`. To avoid retreading the
            // steps of the same types, when the end of a invalid path is reached the
            // type map is added to `excluded`, we then check all values in `excluded`
            // and reduce the sets, e.g. (assuming the only data types are u8, u16 and u32)
            // if `[a:u8,b:u8]`, `[a:u8,b:u8]` and `[a:u8,b:u8]` are present in `excluded` then `[a:u8]` is added.
            let branch = branch_ptr.as_ref();
            let ast = branch.node;

            // Record all the AST node that are reachable.
            touched.insert(ast);

            // let this = &branch.node.as_ref().this;
            // println!("{} {this:?}",branch.hart);

            // Check the instruction is valid and make typing decisions.
            match &branch.node.as_ref().this {
                // Instructions which cannot be invalid and do not affect types.
                Instruction::Li(_)
                | Instruction::Label(_)
                | Instruction::Addi(_)
                | Instruction::Blt(_)
                | Instruction::Csrr(_)
                | Instruction::Bnez(_)
                | Instruction::Beqz(_)
                | Instruction::Wfi(_) => {}
                Instruction::La(La { register: _, label }) => {
                    if !types.contains_key(label) {
                        let next_possible_opt = TYPE_LIST.iter().find(|p| {
                            let mut t = types.clone();
                            t.insert(label.clone(), (*p).clone());
                            !excluded.contains(&t)
                        });
                        if let Some(next_possible) = next_possible_opt {
                            types.insert(label.clone(), next_possible.clone());
                        } else {
                            // When there is no possible type the current types cannot be used
                            // as they lead to this block. So add them to the excluded list and
                            // restart exploration.
                            break 'outer;
                        }
                    }
                }
                // For any store we need to validate the destination is valid.
                Instruction::Sw(Sw {
                    to,
                    from: _,
                    offset,
                }) => {
                    // Find value of the `to` register.
                    let mut current = branch_ptr;
                    while let VerifierPrevNode::Branch(pred) = current.as_ref().prev {
                        match &pred.as_ref().node.as_ref().this {
                            Instruction::La(La { register, label }) => {
                                if register == to {
                                    let var_type = types.get(label).unwrap();
                                    // If attempting to access outside the memory space for the label.
                                    if size(var_type) < 4 + offset.value.value as usize {
                                        // The path is invalid, so we add the current types to the
                                        // excluded list and restart exploration.
                                        break 'outer;
                                    } else {
                                        // We found the label and we can validate that the storing
                                        // of a word with the given offset is within the address space.
                                        // So we continue exploration.
                                        break;
                                    }
                                } else {
                                    todo!()
                                }
                            }
                            Instruction::Li(Li {
                                register,
                                immediate: _,
                            }) => {
                                if register == to {
                                    todo!()
                                }
                            }
                            Instruction::Sw(_) => {}
                            Instruction::Lw(Lw {
                                to: lwto,
                                from: _,
                                offset: _,
                            }) => {
                                if lwto == to {
                                    todo!()
                                }
                            }
                            Instruction::Addi(Addi {
                                out,
                                lhs: _,
                                rhs: _,
                            }) => {
                                if out == to {
                                    todo!()
                                }
                            }
                            x @ _ => todo!("{x:?}"),
                        }
                        current = pred;
                    }
                }
                // For any load we need to validate the destination is valid.
                Instruction::Lw(Lw {
                    to: _,
                    from,
                    offset,
                }) => {
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &types);

                    // Check the destination is valid.
                    match state.registers[branch.hart as usize].get(from) {
                        Some(RegisterValue::Address(from_label)) => {
                            let var_type = types.get(from_label).unwrap();
                            // If attempting to access outside the memory space for the label.
                            if size(var_type) < 4 + offset.value.value as usize {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                break 'outer;
                            } else {
                                // We found the label and we can validate that the loading
                                // of a word with the given offset is within the address space.
                                // So we continue exploration.
                            }
                        }
                        x @ _ => todo!("{x:?}"),
                    }
                }
                Instruction::Lb(Lb {
                    to: _,
                    from,
                    offset,
                }) => {
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &types);

                    // dbg!(from);
                    // dbg!(&state);
                    // for rooter in &root.as_ref().next {
                    //     let tree = crate::draw::draw_tree(*rooter, 1, |x| {
                    //         x.as_ref().node.as_ref().this.to_string()
                    //     });
                    //     println!("{tree}");
                    //     println!();
                    // }

                    // Check the destination is valid.
                    match state.registers[branch.hart as usize].get(from) {
                        Some(RegisterValue::Address(from_label)) => {
                            let var_type = types.get(from_label).unwrap();
                            // If attempting to access outside the memory space for the label.
                            if size(var_type) < 1 + offset.value.value as usize {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                break 'outer;
                            } else {
                                // We found the label and we can validate that the loading
                                // of a word with the given offset is within the address space.
                                // So we continue exploration.
                            }
                        }
                        x @ _ => todo!("{x:?}"),
                    }
                }
                // If any fail is encountered then the path is invalid.
                Instruction::Fail(_) => break 'outer,
                x @ _ => todo!("{x:?}"),
            }
            queue_up(branch_ptr, &mut queue, &types);
        }


        // If we have evaluated all nodes in the queue
        if queue.is_empty() {
            break (types, touched);
        }

        

        // This will only be reached for an invalid path.

        // Since there is an indefinite number of types we can never reduce the types.
        // E.g. you might think if we have excluded `[a:u8,b:u8]` and `[a:u8,b:u16]` (etc.
        // with b being all integer types) we can exclude `[a:u8]` but this doesn't work
        // since lists can be indefinitely long.
        excluded.insert(types.clone());

        // Dealloc the current tree so we can restart.
        for mut root in roots.iter().copied() {
            let stack = &mut root.as_mut().next;
            while let Some(next) = stack.pop() {
                stack.extend(next.as_ref().next.iter());
                dealloc(next.as_ptr().cast(), Layout::new::<VerifierNode>());
            }
        }

        #[cfg(debug_assertions)]
        {
            check += 1;
            println!("{types:?}");
            println!("{excluded:?}");
            if check > 10 {
                panic!();
            }
        }

        // TODO: Don't use a panic here.
        if types.is_empty() {
            panic!("No valid path"); 
        }
    };

    // Remove all AST node not present in `final_touched`.
    todo!();

    // Add the data labels based on `final_types`.
    todo!();

    // When we find a valid path, we also want to clear the tree. When clearing an invalid path
    // we don't clear the roots, but we do here.
    for mut root in roots.into_iter() {
        let stack = &mut root.as_mut().next;
        while let Some(next) = stack.pop() {
            stack.extend(next.as_ref().next.iter());
            dealloc(next.as_ptr().cast(), Layout::new::<VerifierNode>());
        }
        dealloc(root.as_ptr().cast(), Layout::new::<VerifierHarts>());
    }

    // For the lowest number of harts in the range, we explore the tree
    // until finding a valid full path for that number of harts.
    // We then explore the tree for the next number of harts, attempting to
    // find a valid full path with matching variable types (in the future it
    // will also need to find a path with a matching ast, given macro functions).

    // Since the number of types is indefinite (given lists can be of any length)
    // to find the best path through the full tree, we use a greedy approach where
    // we return the first valid path we find, we always pick the best (smallest)
    // possible variable at each stage, only exploring other variables if we find
    // this type doesn't form a valid path.

    // When we find a path is invalid, we discard/deallocate already explored nodes
    // belonging exclusively to this invalid path and we store the intersection of
    // types as invalid (if x:u8,y:u16,z:i64 is found as a valid path for 1 hart,
    // but then x:u8,y:u16 is found to be invalid for 2 harts, we store x:u8,y:u16 as
    // invalid, so as soon as we know not to explore any path requiring this later).
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
    types: &Types,
) {
    let (record, root, harts, first_step) = get_backpath_harts(prev);

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

    // The lowest hart non-racy node is enqueued
    // (or possibly multiples nodes in the case of a conditional jump where
    // we cannot deteremine the condition).
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            // Non-racy + Non-conditional
            Instruction::Label(_)
            | Instruction::La(_)
            | Instruction::Li(_)
            | Instruction::Addi(_)
            | Instruction::Csrr(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            // Non-racy + Conditional
            Instruction::Blt(Blt { rhs, lhs, label }) => {
                let state = find_state(&record, root, harts, first_step, types);

                let lhs = state.registers[hart as usize].get(lhs);
                let rhs = state.registers[hart as usize].get(rhs);
                match (lhs, rhs) {
                    (Some(RegisterValue::Immediate(l)), Some(RegisterValue::Immediate(r))) => {
                        if let Some(r) = r.value()
                            && let Some(l) = l.value()
                        {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if l < r {
                                let label_node = find_label(node,label).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(
                                    prev,
                                    node_ref,
                                    hart,
                                ));
                            }
                        } else {
                            todo!()
                        }
                    }
                    _ => todo!(),
                }
                return;
            }
            Instruction::Bnez(Bnez { src, dest }) => {
                let state = find_state(&record, root, harts, first_step, types);

                let src = state.registers[hart as usize].get(src);

                // dbg!(&src);
                match src {
                    Some(RegisterValue::Immediate(imm)) => {
                        if let Some(imm) = imm.value() {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if imm != Immediate::ZERO {
                                let label_node = find_label(node,dest).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(
                                    prev,
                                    node_ref,
                                    hart,
                                ));
                            }
                        } else {
                            todo!()
                        }
                    }
                    Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                        if hart != 0 {
                            let label_node = find_label(node,dest).unwrap();
                            queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                        } else {
                            // dbg!("here");
                            queue.push_back(simple_nonnull(
                                prev,
                                node_ref,
                                hart,
                            ));
                        }
                    }
                    x @ _ => todo!("{x:?}"),
                }
                return;
            }
            Instruction::Beqz(Beqz { register, label }) => {
                let state = find_state(&record, root, harts, first_step, types);

                let src = state.registers[hart as usize].get(register);

                // dbg!(&src);
                match src {
                    Some(RegisterValue::Immediate(imm)) => {
                        if let Some(imm) = imm.value() {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if imm == Immediate::ZERO {
                                let label_node = find_label(node,label).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(
                                    prev,
                                    node_ref,
                                    hart,
                                ));
                            }
                        } else {
                            todo!()
                        }
                    }
                    Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                        if hart == 0 {
                            let label_node = find_label(node,label).unwrap();
                            queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                        } else {
                            // dbg!("here");
                            queue.push_back(simple_nonnull(
                                prev,
                                node_ref,
                                hart,
                            ));
                        }
                    }
                    x @ _ => todo!("{x:?}"),
                }
                return;
            }
            // Racy
            Instruction::Sw(_) | Instruction::Lw(_) | Instruction::Lb(_) => continue,
            // See note on `wfi`.
            Instruction::Wfi(_) => continue,
            x @ _ => todo!("{x:?}"),
        }
    }

    // If all next nodes are racy, then all nodes are enqueued.
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            // Racy
            Instruction::Sw(_) | Instruction::Lw(_) | Instruction::Lb(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            // See note on `wfi`.
            Instruction::Wfi(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            // Since this can only be reached when all nodes are racy, most nodes should not be reachable here.
            x @ _ => unreachable!("{x:?}"),
        }
    }
}

unsafe fn simple_nonnull(
    mut prev: NonNull<VerifierNode>,
    node_ref: &AstNode,
    hart: u8,
) -> NonNull<VerifierNode> {
    let ptr = alloc(Layout::new::<VerifierNode>()).cast();
    ptr::write(
        ptr,
        VerifierNode {
            prev: VerifierPrevNode::Branch(prev),
            hart,
            node: node_ref.next.unwrap(),
            next: Vec::new(),
        },
    );
    let nonull = NonNull::new(ptr).unwrap();
    prev.as_mut().next.push(nonull);
    nonull
}

unsafe fn find_label(node: NonNull<AstNode>, label: &Label) -> Option<NonNull<AstNode>> {
    // Check start
    if let Instruction::Label(LabelInstruction { tag }) = &node.as_ref().this && tag == label {
        return Some(node);
    }

    // Trace backwards.
    let mut back = node;
    while let Some(prev) = back.as_ref().prev {
        if let Instruction::Label(LabelInstruction { tag }) = &prev.as_ref().this && tag == label {
            return Some(prev);
        }
        back = prev;
    }

    // Trace forward.
    let mut front = node;
    while let Some(next) = front.as_ref().next {
        if let Instruction::Label(LabelInstruction { tag }) = &next.as_ref().this && tag == label {
            return Some(next);
        }
        front = next;
    }

    None
}

unsafe fn find_state(
    record: &[usize],
    root: NonNull<VerifierHarts>,
    harts: u8,
    first_step: usize,
    types: &Types,
) -> State {
    // Iterate forward to find the values.
    let mut state = State::new(harts);
    let mut current = root.as_ref().next[first_step];
    for next in record.iter().rev() {
        let vnode = current.as_ref();
        let hart = vnode.hart as usize;
        match &vnode.node.as_ref().this {
            // Instructions with no side affects.
            Instruction::Label(_)
            | Instruction::Blt(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_) => {}
            Instruction::Li(Li {
                register,
                immediate,
            }) => {
                state.registers[hart].insert(*register, RegisterValue::from(*immediate));
            }
            Instruction::La(La { register, label }) => {
                state.registers[hart].insert(*register, RegisterValue::from(label.clone()));
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                let Offset {
                    value: Immediate { value: 0 },
                } = offset
                else {
                    todo!()
                };

                let Some(to_value) = state.registers[hart].get(to) else {
                    todo!()
                };
                let Some(from_value) = state.registers[hart].get(from) else {
                    todo!()
                };
                match to_value {
                    RegisterValue::Address(to_label) => {
                        let to_type = types.get(to_label).unwrap();
                        // We should have already checked the type is large enough for the store.
                        debug_assert!(size(to_type) >= 4);
                        match from_value {
                            RegisterValue::Immediate(from_imm) => {
                                if let Some(imm) = from_imm.value() {
                                    state.memory.set_word(
                                        &MemoryLocation::from(to_label),
                                        <[u8; 4]>::try_from(&imm.to_ne_bytes()[4..8]).unwrap()
                                    );
                                } else {
                                    todo!()
                                }
                            }
                            _ => todo!(),
                        }
                    }
                    _ => todo!(),
                }
            }
            Instruction::Lw(Lw { to, from, offset }) => {
                let Offset {
                    value: Immediate { value: 0 },
                } = offset
                else {
                    todo!()
                };
                let Some(from_value) = state.registers[hart].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(from_label) => {
                        let from_type = types.get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        debug_assert!(size(from_type) >= 4);
                        let Some(word) =
                            state.memory.get_word(&MemoryLocation::from(from_label))
                        else {
                            todo!()
                        };
                        let imm = Immediate::from(*word);
                        state.registers[hart].insert(
                            *to,
                            RegisterValue::Immediate(ImmediateRange(imm..=imm)),
                        );
                    }
                    _ => todo!(),
                }
            }
            Instruction::Lb(Lb { to, from, offset }) => {
                let Offset {
                    value: Immediate { value: 0 },
                } = offset
                else {
                    todo!()
                };
                let Some(from_value) = state.registers[hart].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(from_label) => {
                        let from_type = types.get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        debug_assert!(size(from_type) >= 1);
                        let Some(byte) =
                            state.memory.get_byte(&MemoryLocation::from(from_label))
                        else {
                            todo!("{from_label:?}")
                        };
                        let imm = Immediate::from(*byte);
                        state.registers[hart].insert(
                            *to,
                            RegisterValue::Immediate(ImmediateRange(imm..=imm)),
                        );
                    }
                    _ => todo!(),
                }
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hart].get(lhs).cloned();
                match lhs_value {
                    Some(RegisterValue::Immediate(imm)) => {
                        state.registers[hart].insert(*out, RegisterValue::Immediate(imm + *rhs));
                    }
                    _ => todo!(),
                }
            }
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hart].insert(*dest, RegisterValue::Csr(CsrValue::Mhartid));
                }
                _ => todo!(),
            },
            x @ _ => todo!("{x:?}"),
        }
        current = current.as_ref().next[*next];
    }
    state
}
