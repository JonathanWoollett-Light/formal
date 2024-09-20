use crate::AstNode;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::collections::BTreeSet;
use std::ptr::NonNull;

pub unsafe fn remove_untouched(
    ast: &mut Option<NonNull<AstNode>>,
    touched: &BTreeSet<NonNull<AstNode>>,
) {
    // Remove untouched nodes.
    let mut next = *ast;
    let mut first = true;
    while let Some(current) = next {
        next = current.as_ref().next;
        if !touched.contains(&current) {
            if first {
                *ast = next;
            }
            remove_ast_node(current);
        } else {
            first = false;
        }
    }
}

pub unsafe fn remove_branches(
    ast: &mut Option<NonNull<AstNode>>,
    jumped: &BTreeSet<NonNull<AstNode>>,
) {
    // Remove branches that never jump.
    use crate::Instruction::*;
    let mut next = *ast;
    let mut first = true;
    while let Some(current) = next {
        next = current.as_ref().next;
        match current.as_ref().this {
            Bne(_) | Blt(_) | Beq(_) | Beqz(_) | Bnez(_) | Bge(_) => {
                if !jumped.contains(&current) {
                    if first {
                        *ast = next;
                    }
                    remove_ast_node(current);
                    continue;
                }
            }
            _ => {}
        }
        first = false;
    }
}

unsafe fn remove_ast_node(node: NonNull<AstNode>) {
    let node_ref = node.as_ref();
    if let Some(mut prev) = node_ref.prev {
        prev.as_mut().next = node_ref.next;
    }
    if let Some(mut next) = node_ref.next {
        next.as_mut().prev = node_ref.prev;
    }
    dealloc(node.as_ptr().cast(), Layout::new::<AstNode>());
}
