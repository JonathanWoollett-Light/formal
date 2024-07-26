use crate::ast::*;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
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
/// Each instruction will have a number of possible following instructions.
/// In some cases multiple possible next instructions will need to be checked
/// to form a valid path.
///
/// e.g.
/// ```text
/// if typeof x = u8
///     a
/// b
/// ```
/// is `[[a], [b]]`
///
/// e.g.
/// ```text
//// if x = 1
///     a
/// b
/// ```
/// is `[[a,b]]`
///
/// ### considering multiple harts
///
/// e.g.
/// ```text
/// a
/// x += 1
/// ```
/// is `[[("x += 1", hart 0), ("x += 1", hart 1), ("x += 1", hart 2)]]`
///
/// For leaf nodes where the next nodes to explore haven't been evaluated it will be `None`.
type NextNode = Vec<Vec<NonNull<VerifierNode>>>;

/// We use a tree to trace the execution of the program,
/// then when conditions are required it can resolve them
/// by looking back at the trace.
struct VerifierNode {
    prev: VerifierPrevNode,
    hart: u8,
    node: NonNull<AstNode>,
    next: NextVerifierNode,
}

pub unsafe fn verify(ast: Option<NonNull<AstNode>>, harts_range: Range<u8>) {
    assert!(harts_range.start > 0);
    let mut data = HashMap::<Label, Vec<u8>>::new();
    let mut bss = HashMap::<Label, usize>::new();
    let mut types = HashMap::<Label, Type>::new();

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
    let mut roots = harts_range
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

    loop {
        // Record the current types of variables on the current path.
        let mut types = Types::new();
        let mut branching = HashMap::new();

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
            match &branch.node.as_ref().this {
                // Instructions which cannot be invalid and do not affect types.
                Instruction::Label(_) | Instruction::Addi(_) | Instruction::Blt(_) => {}
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
                Instruction::Li(_) => {
                    // Loading an immediate into a register does nothing by itself.
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
                    // Find value of the `from` register.
                    let mut current = branch_ptr;
                    while let VerifierPrevNode::Branch(pred) = current.as_ref().prev {
                        match &pred.as_ref().node.as_ref().this {
                            Instruction::La(La { register, label }) => {
                                if register == from {
                                    let var_type = types.get(label).unwrap();
                                    // If attempting to access outside the memory space for the label.
                                    if size(var_type) < 4 + offset.value.value as usize {
                                        // The path is invalid, so we add the current types to the
                                        // excluded list and restart exploration.
                                        break 'outer;
                                    } else {
                                        // We found the label and we can validate that the loading
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
                                if register == from {
                                    todo!()
                                }
                            }

                            Instruction::Sw(_) => {}
                            Instruction::Lw(Lw {
                                to: lwto,
                                from: _,
                                offset: _,
                            }) => {
                                if lwto == from {
                                    todo!()
                                }
                            }
                            Instruction::Addi(Addi {
                                out,
                                lhs: _,
                                rhs: _,
                            }) => {
                                if out == from {
                                    todo!()
                                }
                            }
                            x @ _ => todo!("{x:?}"),
                        }
                        current = pred;
                    }
                }
                x @ _ => todo!("{x:?}"),
            }
            queue_up(branch_ptr, &mut queue, &mut branching);
        }

        // If we have evaluated all nodes in the queue
        if queue.is_empty() {
            break;
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
    }

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

type Types = BTreeMap<Label, Type>;
type Excluded = HashSet<BTreeMap<Label, Type>>;

#[derive(Debug, Eq, PartialEq, PartialOrd, Ord, Clone, Copy)]
enum Branching {
    True,
    False,
    Both,
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
    branches: &mut HashMap<NonNull<AstNode>, Branching>,
) {
    // Get the number of harts of this sub-tree and record the path.
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
            | Instruction::Addi(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            // Non-racy + Conditional
            Instruction::Blt(Blt { rhs, lhs, label }) => {
                #[derive(Debug, Clone, Eq, PartialEq, PartialOrd, Ord, Hash)]
                enum Lhs {
                    Label(Label),
                    Register(Register),
                }
                #[derive(Debug, Clone)]
                struct Domain {
                    range: RangeInclusive<Immediate>,
                }
                impl From<Immediate> for Domain {
                    fn from(x: Immediate) -> Self {
                        Self { range: x..=x }
                    }
                }

                // Iterate forward to find the values.
                let mut values = HashMap::new();
                let mut current = root.as_ref().next[first_step];
                for next in record.iter().rev() {
                    match current.as_ref().node.as_ref().this {
                        Instruction::Li(Li {
                            register,
                            immediate,
                        }) => {
                            values.insert(Lhs::Register(register), Domain::from(immediate));
                        }
                        _ => todo!(),
                    }
                    current = current.as_ref().next[*next];
                }

                todo!();
                return;
            }
            // Racy
            Instruction::Sw(_) | Instruction::Lw(_) => continue,
            x @ _ => todo!("{x:?}"),
        }
    }

    // If all next nodes are racy, then all nodes are enqueued.
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            // Non-conditional
            Instruction::Sw(_) | Instruction::Lw(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            // Racy
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
