use crate::ast::*;
use std::alloc::Layout;
use std::collections::BTreeMap;
use std::collections::HashSet;
use std::num::NonZeroU8;
use std::ops::Range;
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

struct VerifierHarts {
    harts: u8,
}

enum VerifierPrevNode {
    Branch(NonNull<VerifierNode>),
    Root(NonNull<VerifierHarts>),
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

    // When we have 1..=3 harts the initial queue will contain
    // `[(_start, hart 0), (_start, hart 0), (_start, hart 0)]`
    // where each entry has a number of predeccessors e.g. `(_start, hart 1)`
    // up to the number of harts for that path.
    let mut queue = harts_range
        .map(|harts| {
            let root = {
                let ptr = alloc(Layout::new::<VerifierHarts>()).cast();
                ptr::write(ptr, VerifierHarts { harts });
                NonNull::new(ptr).unwrap()
            };
            // All harts are intiailized as `_start`.
            let last =
                (0..harts)
                    .into_iter()
                    .rev()
                    .fold(VerifierPrevNode::Root(root), |prev, hart| {
                        let nonull = {
                            let ptr = alloc(Layout::new::<VerifierNode>()).cast();
                            ptr::write(
                                ptr,
                                VerifierNode {
                                    prev,
                                    hart,
                                    node: second_ptr,
                                },
                            );
                            NonNull::new(ptr).unwrap()
                        };
                        VerifierPrevNode::Branch(nonull)
                    });
            let VerifierPrevNode::Branch(branch) = last else {
                unreachable!()
            };
            branch
        })
        .collect::<VecDeque<_>>();

    // Since `HashMap` doesn't implement `Hash` we use `BTreeMap`.
    let mut types = BTreeMap::<Label, Type>::new();
    let mut excluded = HashSet::<BTreeMap<Label, Type>>::new();

    while let Some(branch_ptr) = queue.pop_front() {
        // If a variable is used that has not yet been defined, add the cheapest
        // possible data type for this variable to `types`. To avoid retreading the
        // steps of the same types, when the end of a invalid path is reached the
        // type map is added to `excluded`, we then check all values in `excluded`
        // and reduce the sets, e.g. (assuming the only data types are u8, u16 and u32)
        // if `[a:u8,b:u8]`, `[a:u8,b:u8]` and `[a:u8,b:u8]` are present in `excluded` then `[a:u8]` is added.
        let branch = branch_ptr.as_ref();
        match &branch.node.as_ref().this {
            Instruction::Label(_) => {
                // Labels by themselves do nothing.
            }
            Instruction::La(La { register: _, label }) => {
                if !types.contains_key(label) {
                    let next_possible_opt = type_list().into_iter().find(|p| {
                        let mut t = types.clone();
                        t.insert(label.clone(), p.clone());
                        !excluded.contains(&t)
                    });
                    if let Some(next_possible) = next_possible_opt {
                        types.insert(label.clone(), next_possible);
                    } else {
                        // Handle the case where there is no possible type.
                        todo!()
                    }
                }
            }
            Instruction::Li(_) => {
                // Loading an immediate into a register does nothing by itself.
            }
            x @ _ => todo!("{x:?}"),
        }
        queue_up(branch_ptr, &mut queue);
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

/// Queues up the next node to evaluate.
///
/// We look at the next node for the 1st hart and queue this up if its not racy,
/// if its racy, we look at the 2nd hart and queue it up if its not racy,
/// if its racy we look at the 3rd hart etc. If all next nodes are racy, we queue
/// up all racy instructions (since we need to evaluate all the possible ordering of them).
unsafe fn queue_up(prev: NonNull<VerifierNode>, queue: &mut VecDeque<NonNull<VerifierNode>>) {
    // Get the number of harts of this sub-tree
    let mut root = prev;
    while let VerifierPrevNode::Branch(branch) = root.as_ref().prev {
        root = branch
    }
    let VerifierPrevNode::Root(root) = root.as_ref().prev else {
        unreachable!()
    };
    let harts = root.as_ref().harts;

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

    unsafe fn simple_nonnull(
        prev: NonNull<VerifierNode>,
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
            },
        );
        NonNull::new(ptr).unwrap()
    }

    // The lowest hart non-racy node is enqueued
    // (or possibly multiples nodes in the case of a conditional jump where we cannot deteremine the condition).
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            Instruction::Label(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            Instruction::La(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            Instruction::Li(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
                return;
            }
            x @ _ => todo!("{x:?}"),
        }
    }

    // If all next nodes are racy, then all nodes are enqueued.
    for (hart, node) in fronts.iter().map(|(a, b)| (*a, *b)) {
        let node_ref = node.as_ref();
        match &node_ref.this {
            Instruction::Label(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            Instruction::La(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            Instruction::Li(_) => {
                queue.push_back(simple_nonnull(prev, node_ref, hart));
            }
            x @ _ => todo!("{x:?}"),
        }
    }
}
