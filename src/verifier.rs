use crate::ast::*;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::hash::Hash;
use std::iter::once;
use std::ops::Range;
use std::ops::RangeInclusive;
use std::ptr;
use std::{
    alloc::alloc,
    collections::{HashMap, VecDeque},
    ptr::NonNull,
};

/// Compile time size
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
        List(_) => 3 * size(&Type::U64),
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
use std::iter::Peekable;
type Types = BTreeMap<Label, Type>;

#[derive(Debug)]
struct MemoryMap {
    map: HashMap<Label, MemoryValue>,
}

impl MemoryMap {
    fn get_byte(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<&u8> {
        let value = self.map.get(tag)?;
        match value {
            MemoryValue::Ascii(ascii) => ascii.get(*offset),
            MemoryValue::Word(word) => word.get(*offset),
            _ => todo!(),
        }
    }
    fn get_word(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<&[u8; 4]> {
        let value = self.map.get(tag)?;
        match value {
            MemoryValue::Word(word) => (*offset == 0).then_some(word),
            _ => todo!(),
        }
    }
    fn get_doubleword(&self, MemoryLocation { tag, offset }: &MemoryLocation) -> Option<[u8; 8]> {
        let value = self.map.get(tag)?;
        match value {
            MemoryValue::DoubleWord(doubleword) => (*offset == 0).then_some(*doubleword),
            MemoryValue::Type(typetype) => match offset {
                0 => Some((typetype.type_value as u64).to_ne_bytes()),
                // The address is a label which cannot be known at comptime.
                1 => todo!(),
                2 => Some((typetype.length as u64).to_ne_bytes()),
                // An offset outside the type is invalid.
                _ => todo!(),
            },
            x => todo!("{x:?}"),
        }
    }
    fn set_word(&mut self, MemoryLocation { tag, offset }: &MemoryLocation, value: [u8; 4]) {
        if let Some(existing) = self.map.get_mut(tag) {
            match existing {
                MemoryValue::Word(word) => {
                    *word = value;
                }
                _ => todo!(),
            }
        } else if *offset == 0 {
            self.map.insert(tag.clone(), MemoryValue::Word(value));
        } else {
            todo!()
        }
    }
    // TODO This should be improved, I'm pretty sure the current approach is bad.
    fn set_type(
        &mut self,
        value: &Type,
        tag_iter: &mut Peekable<impl Iterator<Item = Label>>, // Iterator to generate unique tags.
    ) -> Label {
        let mut vec = Vec::new();
        vec.push((None, value.clone()));
        let mut right = 0;
        // Fill queue with all types
        while right < vec.len() {
            if let Type::List(list) = &vec[right].1 {
                for offset in 0..list.len() {
                    let t = vec[right].1.list_mut()[offset].clone();
                    vec.insert(right + offset + 1, (None, t));
                }
            }
            right += 1;
        }
        println!();
        println!("map: {:?}", self.map);
        println!();
        println!("vec: {vec:?}");

        let mut left = right;
        while left > 0 {
            left -= 1;
            if let (None, Type::List(_)) = &vec[left] {
                let memory_types = vec
                    .drain(left + 1..right)
                    .map(|(addr, t)| MemoryValueType {
                        type_value: FlatType::from(&t),
                        addr,
                        length: if let Type::List(l) = &t { l.len() } else { 0 },
                    })
                    .collect::<Vec<_>>();
                let tag = tag_iter.next().unwrap();
                vec[left].0 = Some(tag.clone());
                self.map.insert(tag, MemoryValue::Types(memory_types));
                right = left;
            }
        }

        println!();
        println!("map: {:?}", self.map);

        let final_tag = tag_iter.next().unwrap();
        match vec.remove(0) {
            (addr @ Some(_), Type::List(list)) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::Type(MemoryValueType {
                        type_value: FlatType::List,
                        addr,
                        length: list.len(),
                    }),
                );
            }
            (None, t) => {
                self.map.insert(
                    final_tag.clone(),
                    MemoryValue::Type(MemoryValueType {
                        type_value: FlatType::from(t),
                        addr: None,
                        length: 0,
                    }),
                );
            }
            _ => unreachable!(),
        }

        println!();
        println!("map: {:?}", self.map);

        final_tag
    }
}

#[derive(Debug)]
struct State {
    // Each hart has its own registers.
    registers: Vec<HashMap<Register, RegisterValue>>,
    memory: MemoryMap,
    // Each hart has its own types. It is possible that
    // 2 harts can treat the same variables as a different
    // type at the same instruction.
    types: BTreeMap<u8, Types>,
}
impl State {
    fn new(harts: u8, initial_types: &BTreeMap<u8, Types>) -> Self {
        Self {
            registers: (0..harts).map(|_| HashMap::new()).collect(),
            memory: MemoryMap {
                map: HashMap::new(),
            },
            types: initial_types.clone(),
        }
    }
}

#[derive(Debug, Eq, PartialEq, Hash, Clone)]
#[non_exhaustive]
struct MemoryLocation {
    tag: Label,
    offset: usize,
}
impl From<Label> for MemoryLocation {
    fn from(tag: Label) -> Self {
        Self { tag, offset: 0 }
    }
}

// It is possible to technically store a 4 byte virtual value (e.g. DATA_END)
// then edit 2 bytes of it. So we will need additional complexity to support this case
#[derive(Debug)]
enum MemoryValue {
    Type(MemoryValueType),
    Types(Vec<MemoryValueType>),
    DoubleWord([u8; 8]),
    Word([u8; 4]),
    Ascii(Vec<u8>),
}

use std::mem::transmute;

#[derive(Debug)]
struct MemoryValueType {
    // null = { 0, 0, 0 }
    // u8 = { 1, 0, 0 }
    // [u8,i16] = { 2, 0xABCD, 2 }
    // etc.
    type_value: FlatType,
    addr: Option<Label>,
    length: usize,
}
impl MemoryValueType {
    unsafe fn to_bytes(self) -> [u8; size_of::<Self>()] {
        transmute(self)
    }
    unsafe fn from_bytes(bytes: [u8; size_of::<Self>()]) -> Self {
        transmute(bytes)
    }
}

#[derive(Debug, Clone)]
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

pub struct Explorerer {

}
impl Explorerer {
    pub fn new(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) -> Self {
        todo!()
    }
    pub fn next_step(&mut self) {
        todo!()
    }
    pub fn next_path(&mut self) {
        todo!()
    }
}

pub unsafe fn verify(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) {
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

    // Record the types of variables we have previously found form invalid paths.
    let mut excluded = HashSet::new();

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

    #[cfg(debug_assertions)]
    let mut check = 0;
    let (final_types, final_touched) = loop {
        // Record the initial types used for variables in this verification path.
        // Different harts can treat the same variables as different types, they have
        // different inputs and often follow different execution paths (effectively having a different AST).
        let mut initial_types = harts_range
            .clone()
            .map(|harts| (harts - 1, Types::new()))
            .collect::<BTreeMap<_, _>>();
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
            let hart = branch.hart;

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
                | Instruction::Wfi(_) => {}
                // If the first encounter of a variable is a cast, we simply add this as the
                // assumed initial type.
                Instruction::Cast(Cast { label, cast }) => {
                    // If the type doesn't have an existing initial type entry, add the initial type as `cast`.
                    initial_types
                        .get_mut(&hart)
                        .unwrap()
                        .entry(label.clone())
                        .or_insert(cast.clone());
                }
                Instruction::Lat(Lat { register: _, label }) => {
                    // TODO We need to update initial types to include `Type::List([u64,u64,u64])` for the type type that describes `label` here.
                    if !initial_types.get(&hart).unwrap().contains_key(label) {
                        let next_possible_opt = TYPE_LIST.iter().find(|p| {
                            let mut test_initial_types = initial_types.clone();
                            test_initial_types
                                .get_mut(&hart)
                                .unwrap()
                                .insert(label.clone(), (*p).clone());
                            !excluded.contains(&test_initial_types)
                        });
                        if let Some(next_possible) = next_possible_opt {
                            initial_types
                                .get_mut(&hart)
                                .unwrap()
                                .insert(label.clone(), next_possible.clone());
                        } else {
                            // When there is no possible type the current types cannot be used
                            // as they lead to this block. So add them to the excluded list and
                            // restart exploration.
                            break 'outer;
                        }
                    }
                }
                Instruction::La(La { register: _, label }) => {
                    if !initial_types.get(&hart).unwrap().contains_key(label) {
                        let next_possible_opt = TYPE_LIST.iter().find(|p| {
                            let mut test_initial_types = initial_types.clone();
                            test_initial_types
                                .get_mut(&hart)
                                .unwrap()
                                .insert(label.clone(), (*p).clone());
                            !excluded.contains(&test_initial_types)
                        });
                        if let Some(next_possible) = next_possible_opt {
                            initial_types
                                .get_mut(&hart)
                                .unwrap()
                                .insert(label.clone(), next_possible.clone());
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
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &initial_types);

                    // Check the destination is valid.
                    match state.registers[hart as usize].get(to) {
                        Some(RegisterValue::Address(from_label)) => {
                            // The current types for the current hart (each hart may treat varioables as different types at different points).
                            let current_local_types = state.types.get(&hart).unwrap();
                            // The type of the variable in question (at this point on this hart).
                            let var_type = current_local_types.get(from_label).unwrap();
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
                        x => todo!("{x:?}"),
                    }
                }
                // For any load we need to validate the destination is valid.
                Instruction::Ld(Ld {
                    to: _,
                    from,
                    offset,
                }) => {
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &initial_types);

                    // Check the destination is valid.
                    match state.registers[branch.hart as usize].get(from) {
                        Some(RegisterValue::Address(from_label)) => {
                            // The current types for the current hart (each hart may treat varioables as different types at different points).
                            let current_local_types = state.types.get(&hart).unwrap();
                            // The type of the variable in question (at this point on this hart).
                            let var_type = current_local_types.get(from_label).unwrap();
                            // If attempting to access outside the memory space for the label.
                            if size(var_type) < 8 + offset.value.value as usize {
                                // The path is invalid, so we add the current types to the
                                // excluded list and restart exploration.
                                break 'outer;
                            } else {
                                // We found the label and we can validate that the loading
                                // of a word with the given offset is within the address space.
                                // So we continue exploration.
                            }
                        }
                        x => todo!("{x:?}"),
                    }
                }
                Instruction::Lw(Lw {
                    to: _,
                    from,
                    offset,
                }) => {
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &initial_types);

                    // Check the destination is valid.
                    match state.registers[branch.hart as usize].get(from) {
                        Some(RegisterValue::Address(from_label)) => {
                            // The current types for the current hart (each hart may treat varioables as different types at different points).
                            let current_local_types = state.types.get(&hart).unwrap();
                            // The type of the variable in question (at this point on this hart).
                            let var_type = current_local_types.get(from_label).unwrap();
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
                        x => todo!("{x:?}"),
                    }
                }
                Instruction::Lb(Lb {
                    to: _,
                    from,
                    offset,
                }) => {
                    // Collect the state.
                    let (record, root, harts, first_step) = get_backpath_harts(branch_ptr);
                    let state = find_state(&record, root, harts, first_step, &initial_types);

                    // Check the destination is valid.
                    match state.registers[branch.hart as usize].get(from) {
                        Some(RegisterValue::Address(from_label)) => {
                            // The current types for the current hart (each hart may treat varioables as different types at different points).
                            let current_local_types = state.types.get(&hart).unwrap();
                            // The type of the variable in question (at this point on this hart).
                            let var_type = current_local_types.get(from_label).unwrap();
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
                        x => todo!("{x:?}"),
                    }
                }
                // If any fail is encountered then the path is invalid.
                Instruction::Fail(_) => break 'outer,
                x => todo!("{x:?}"),
            }
            queue_up(branch_ptr, &mut queue, &initial_types);
        }

        // If we have evaluated all nodes in the queue
        if queue.is_empty() {
            break (initial_types, touched);
        }

        // This will only be reached for an invalid path.

        // Since there is an indefinite number of types we can never reduce the types.
        // E.g. you might think if we have excluded `[a:u8,b:u8]` and `[a:u8,b:u16]` (etc.
        // with b being all integer types) we can exclude `[a:u8]` but this doesn't work
        // since lists can be indefinitely long.
        excluded.insert(initial_types.clone());

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
            dbg!();
            println!("{initial_types:?}");
            println!("{excluded:?}");
            dbg!();
            if check > 100 {
                panic!();
            }
        }

        // TODO Make this explanation better.
        // This case only occurs when all types are excluded thus it continually breaks out
        // of the exploration loop with empty `initial_types`. This case means there is no
        // valid type combination and thus no valid path.
        // TODO: Don't use a panic here.
        if initial_types.is_empty() {
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
    // When a variable is first encountered it is treated as this type.
    initial_types: &BTreeMap<u8, Types>,
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
            // Non-racy + Non-conditional.
            Instruction::Label(_)
            | Instruction::La(_)
            | Instruction::Lat(_)
            | Instruction::Li(_)
            | Instruction::Addi(_)
            | Instruction::Csrr(_)
            | Instruction::Cast(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            // Non-racy + Conditional.
            Instruction::Blt(Blt { rhs, lhs, label }) => {
                let state = find_state(&record, root, harts, first_step, initial_types);

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
                                let label_node = find_label(node, label).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(prev, node_ref, hart));
                            }
                        } else {
                            todo!()
                        }
                    }
                    _ => todo!(),
                }
                return;
            }
            Instruction::Bne(Bne { rhs, lhs, out }) => {
                let state = find_state(&record, root, harts, first_step, initial_types);

                let lhs = state.registers[hart as usize].get(lhs);
                let rhs = state.registers[hart as usize].get(rhs);
                match (lhs, rhs) {
                    (Some(RegisterValue::Immediate(l)), Some(RegisterValue::Immediate(r))) => {
                        if let Some(r) = r.value()
                            && let Some(l) = l.value()
                        {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if l != r {
                                let label_node = find_label(node, out).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(prev, node_ref, hart));
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
                let state = find_state(&record, root, harts, first_step, initial_types);

                let src = state.registers[hart as usize].get(src);

                match src {
                    Some(RegisterValue::Immediate(imm)) => {
                        if let Some(imm) = imm.value() {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if imm != Immediate::ZERO {
                                let label_node = find_label(node, dest).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(prev, node_ref, hart));
                            }
                        } else {
                            todo!()
                        }
                    }
                    Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                        if hart != 0 {
                            let label_node = find_label(node, dest).unwrap();
                            queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                        } else {
                            // dbg!("here");
                            queue.push_back(simple_nonnull(prev, node_ref, hart));
                        }
                    }
                    x => todo!("{x:?}"),
                }
                return;
            }
            Instruction::Beqz(Beqz { register, label }) => {
                let state = find_state(&record, root, harts, first_step, initial_types);

                let src = state.registers[hart as usize].get(register);

                // dbg!(&src);
                match src {
                    Some(RegisterValue::Immediate(imm)) => {
                        if let Some(imm) = imm.value() {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if imm == Immediate::ZERO {
                                let label_node = find_label(node, label).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(prev, node_ref, hart));
                            }
                        } else {
                            todo!()
                        }
                    }
                    Some(RegisterValue::Csr(CsrValue::Mhartid)) => {
                        if hart == 0 {
                            let label_node = find_label(node, label).unwrap();
                            queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                        } else {
                            // dbg!("here");
                            queue.push_back(simple_nonnull(prev, node_ref, hart));
                        }
                    }
                    x => todo!("{x:?}"),
                }
                return;
            }
            Instruction::Bge(Bge { lhs, rhs, out }) => {
                let state = find_state(&record, root, harts, first_step, initial_types);

                let lhs = state.registers[hart as usize].get(lhs);
                let rhs = state.registers[hart as usize].get(rhs);
                match (lhs, rhs) {
                    (Some(RegisterValue::Immediate(l)), Some(RegisterValue::Immediate(r))) => {
                        if let Some(r) = r.value()
                            && let Some(l) = l.value()
                        {
                            // Since in this case the path is determinate, we either queue up the label or the next ast node and
                            // don't need to actually visit/evaluate the branch at runtime.
                            if l > r {
                                let label_node = find_label(node, out).unwrap();
                                queue.push_back(simple_nonnull(prev, label_node.as_ref(), hart));
                            } else {
                                queue.push_back(simple_nonnull(prev, node_ref, hart));
                            }
                        } else {
                            todo!()
                        }
                    }
                    _ => todo!(),
                }
                return;
            }
            // Racy.
            Instruction::Sw(_) | Instruction::Ld(_) | Instruction::Lw(_) | Instruction::Lb(_) => {
                continue
            }
            // See note on `wfi`.
            Instruction::Wfi(_) => continue,
            // Blocking.
            Instruction::Unreachable(_) => continue,
            x => todo!("{x:?}"),
        }
    }

    // If all next nodes are racy, then all nodes are enqueued.
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            // Racy.
            Instruction::Sw(_) | Instruction::Ld(_) | Instruction::Lw(_) | Instruction::Lb(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            // See note on `wfi`.
            Instruction::Wfi(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            // Blocking.
            Instruction::Unreachable(_) => continue,
            // Since this can only be reached when all nodes are racy, most nodes should not be reachable here.
            x => unreachable!("{x:?}"),
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
    if let Instruction::Label(LabelInstruction { tag }) = &node.as_ref().this
        && tag == label
    {
        return Some(node);
    }

    // Trace backwards.
    let mut back = node;
    while let Some(prev) = back.as_ref().prev {
        if let Instruction::Label(LabelInstruction { tag }) = &prev.as_ref().this
            && tag == label
        {
            return Some(prev);
        }
        back = prev;
    }

    // Trace forward.
    let mut front = node;
    while let Some(next) = front.as_ref().next {
        if let Instruction::Label(LabelInstruction { tag }) = &next.as_ref().this
            && tag == label
        {
            return Some(next);
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
    initial_types: &BTreeMap<u8, Types>, // Initial types for variables for each thread.
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
    let mut state = State::new(harts, initial_types);
    let mut current = root.as_ref().next[first_step];
    for (count, next) in record.iter().rev().enumerate() {
        let vnode = current.as_ref();
        let hart = vnode.hart;
        let hartu = hart as usize;
        match &vnode.node.as_ref().this {
            // Instructions with no side affects.
            Instruction::Label(_)
            | Instruction::Blt(_)
            | Instruction::Bnez(_)
            | Instruction::Beqz(_)
            | Instruction::Bge(_) => {}
            Instruction::Cast(Cast { label, cast }) => {
                // If the first encountered instance of a variable is a cast, the initial
                // type will still be added, using the type specified in the cast.
                *state.types.get_mut(&hart).unwrap().get_mut(label).unwrap() = cast.clone();
            }
            Instruction::Li(Li {
                register,
                immediate,
            }) => {
                state.registers[hartu].insert(*register, RegisterValue::from(*immediate));
            }
            Instruction::Lat(Lat { register, label }) => {
                let typeof_type = state.types.get(&hart).unwrap().get(label).unwrap();
                let loc = state.memory.set_type(typeof_type, &mut tag_iter);
                state.registers[hartu].insert(*register, RegisterValue::Address(loc.clone()));

                // Each type type should have its own unique label.
                let existing = state
                    .types
                    .get_mut(&hart)
                    .unwrap()
                    .insert(loc, Type::List(vec![Type::U64, Type::U64, Type::U64]));
                debug_assert!(existing.is_none());
            }
            Instruction::La(La { register, label }) => {
                state.registers[hartu].insert(*register, RegisterValue::from(label.clone()));
            }
            Instruction::Sw(Sw { to, from, offset }) => {
                let Offset {
                    value: Immediate { value: 0 },
                } = offset
                else {
                    todo!()
                };

                let Some(to_value) = state.registers[hartu].get(to) else {
                    todo!()
                };
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match to_value {
                    RegisterValue::Address(to_label) => {
                        let to_type = state.types.get(&hart).unwrap().get(to_label).unwrap();
                        // We should have already checked the type is large enough for the store.
                        debug_assert!(size(to_type) >= 4);
                        match from_value {
                            RegisterValue::Immediate(from_imm) => {
                                if let Some(imm) = from_imm.value() {
                                    state.memory.set_word(
                                        &MemoryLocation::from(to_label.clone()),
                                        <[u8; 4]>::try_from(&imm.to_ne_bytes()[4..8]).unwrap(),
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
            Instruction::Ld(Ld { to, from, offset }) => {
                let Offset {
                    value: Immediate { value: 0 },
                } = offset
                else {
                    todo!()
                };
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(from_label) => {
                        let from_type = state.types.get(&hart).unwrap().get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        debug_assert!(size(from_type) >= 8);
                        let Some(doubleword) = state
                            .memory
                            .get_doubleword(&MemoryLocation::from(from_label.clone()))
                        else {
                            todo!()
                        };
                        let imm = Immediate::from(doubleword);
                        state.registers[hartu]
                            .insert(*to, RegisterValue::Immediate(ImmediateRange(imm..=imm)));
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
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(from_label) => {
                        let from_type = state.types.get(&hart).unwrap().get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        debug_assert!(size(from_type) >= 4);
                        let Some(word) = state
                            .memory
                            .get_word(&MemoryLocation::from(from_label.clone()))
                        else {
                            todo!()
                        };
                        let imm = Immediate::from(*word);
                        state.registers[hartu]
                            .insert(*to, RegisterValue::Immediate(ImmediateRange(imm..=imm)));
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
                let Some(from_value) = state.registers[hartu].get(from) else {
                    todo!()
                };
                match from_value {
                    RegisterValue::Address(from_label) => {
                        let from_type = state.types.get(&hart).unwrap().get(from_label).unwrap();
                        // We should have already checked the type is large enough for the load.
                        debug_assert!(size(from_type) >= 1);
                        let Some(byte) = state
                            .memory
                            .get_byte(&MemoryLocation::from(from_label.clone()))
                        else {
                            todo!("{from_label:?}")
                        };
                        let imm = Immediate::from(*byte);
                        state.registers[hartu]
                            .insert(*to, RegisterValue::Immediate(ImmediateRange(imm..=imm)));
                    }
                    _ => todo!(),
                }
            }
            Instruction::Addi(Addi { out, lhs, rhs }) => {
                let lhs_value = state.registers[hartu].get(lhs).cloned();
                match lhs_value {
                    Some(RegisterValue::Immediate(imm)) => {
                        state.registers[hartu].insert(*out, RegisterValue::Immediate(imm + *rhs));
                    }
                    _ => todo!(),
                }
            }
            Instruction::Csrr(Csrr { dest, src }) => match src {
                Csr::Mhartid => {
                    state.registers[hartu].insert(*dest, RegisterValue::Csr(CsrValue::Mhartid));
                }
                _ => todo!(),
            },
            // TODO Some interrupt state is likely affected here so this needs to be added.
            Instruction::Wfi(_) => {}
            x => todo!("{x:?}"),
        }
        current = current.as_ref().next[*next];
    }
    state
}
