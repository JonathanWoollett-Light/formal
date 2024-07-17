use crate::ast::*;
use std::{alloc::alloc, collections::HashMap, ptr::NonNull};
use std::alloc::Layout;
use std::ptr;

// Where ordering is important `Vec` will be used,
// where it is not important `UnorderedVec` will be used.
#[derive(Debug)]
struct UnorderedVec<T>(Vec<T>);

#[derive(Debug)]
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
        _ => todo!()
    }
}

fn any_type() -> Vec<Type> {
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

// We use a tree to trace the execution of the program,
// then when conditions are required it can resolve them
// by looking back at the trace.
struct VerifierNode {
    prev: Option<NonNull<VerifierNode>>,
    hart: u8,
    node: NonNull<AstNode>,
    // Each instruction will have a number of possible following instructions.
    // In some cases multiple possible next instructions will need to be checked
    // to form a valid path.
    //
    // e.g.
    // ```text
    // if typeof x = u8
    //     a
    // b
    // ```
    // is `[[a], [b]]`
    // 
    // e.g.
    // ```text
    // if x = 1
    //     a
    // b
    // ```
    // is `[[a,b]]`
    //
    // ### considering multiple harts
    //
    // e.g.
    // ```text
    // a
    // x += 1
    // ```
    // is `[[("x += 1", hart 0), ("x += 1", hart 1), ("x += 1", hart 2)]]`
    //
    // For leaf nodes where the next nodes to explore haven't been evaluated it will be `None`.
    next: Option<UnorderedVec<UnorderedVec<NonNull<VerifierNode>>>>
}

// The current leaves the of tree of possible executions.
struct Front {
    // Each hart has a different position in execution, we advance by advancing
    // each hart until they all reach racy instructions.
    harts: Vec<NonNull<VerifierNode>>
}

pub unsafe fn verify(ast: Option<NonNull<AstNode>>, max_harts: u8) {
    let mut harts = 1;
    let mut data = HashMap::<Label, Vec<u8>>::new();
    let mut bss = HashMap::<Label, usize>::new();
    let mut types = HashMap::<Label, Type>::new();

    // Intial misc stuff
    let first = ast.unwrap().as_ref();
    let second = first.next.unwrap();
    match first.this {
        Instruction::Global(Global { tag: start_tag }) => {
            match second.as_ref().this {
                Instruction::Label(LabelInstruction { tag }) => {
                    assert_eq!(start_tag, tag);
                }
                _ => panic!("The second node must be the start label"),
            }
        }
        _ => panic!("The first node must be the global start label definition"),
    }
    
    // All traces start with hart 0 at `_start:`.
    let front = {
        let ptr = alloc(Layout::new::<VerifierNode>()).cast();
        ptr::write(ptr, VerifierNode {
            prev: None,
            hart: 0,
            node: second,
            next: None
        });
        NonNull::new(ptr).unwrap()
    };
    let mut stack = vec![front];
    

    let mut first_stack = Vec::new();
    match unsafe { &front.as_ref().this } {
        Instruction::La(La { register: _, label }) => {
            let opt = types.get(label);
            match opt {
                None => {
                    first_stack.extend(any_type().into_iter().map(|t| (label.clone(), t)));
                    front = unsafe { front.as_ref().next.unwrap() };
                }
                _ => todo!(),
            }
        }
        _ => todo!(),
    }

    match unsafe { &front.as_ref().this } {
        Instruction::Li(_) => {
            front = unsafe { front.as_ref().next.unwrap() };
        }
        _ => todo!(),
    }

    match unsafe { &front.as_ref().this } {
        Instruction::Sw(Sw { to, from, offset }) => {
            // With any store we need to verify that the address at which it is attempting
            // to store is valid.
            //
            // Here we back in the AST for the source of `to`, in this case it is a variable,
            // we then check the variable is large enough to store `.word`.
            //
            // Although it is possible that it is safe to allocate to a label with a
            // smaller size (there might be another variable after etc.) we don't consider
            // this case. It is easier to verify assuming this is unsafe and I don't think
            // people really need this use-case.
            let mut current = front;
            let mut dest = None;
            while let Some(prev) = unsafe { current.as_ref().prev } {
                match unsafe { &prev.as_ref().this } {
                    Instruction::La(La { register, label }) => {
                        if register == to {
                            dest = Some(label.clone());
                            break;
                        }
                    }
                    Instruction::Li(Li { register, immediate: _ }) => {
                        if register == to {
                            todo!()
                        }
                        else {
                        }
                    }
                    _ => todo!(),
                }
                current = prev;
            }
            // Assert the variable is larger than or equal to a word.
            assert!(size(&first_stack[0].1) >= 4);
        }
        _ => todo!(),
    }
}
