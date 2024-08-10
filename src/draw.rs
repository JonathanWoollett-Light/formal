use crate::ast::*;
use crate::verifier::*;
use std::alloc::dealloc;
use std::alloc::Layout;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::collections::BTreeSet;
use std::collections::HashSet;
use std::hash::Hash;
use std::iter;
use std::iter::repeat;
use std::num::NonZeroU8;
use std::ops::Bound::{Excluded, Included};
use std::ops::Range;
use std::ops::RangeInclusive;
use std::ptr;
use std::{
    alloc::alloc,
    collections::{HashMap, VecDeque},
    ptr::NonNull,
};

#[derive(Debug, Eq, PartialEq, Clone, Copy)]
struct Coordinate {
    x: usize,
    y: usize,
}

impl Ord for Coordinate {
    fn cmp(&self, other: &Self) -> Ordering {
        match self.y.cmp(&other.y) {
            Ordering::Equal => self.x.cmp(&other.x),
            ord @ (Ordering::Less | Ordering::Greater) => ord,
        }
    }
}

impl PartialOrd for Coordinate {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

type Type = NonNull<VerifierNode>;

/// Draws a tree.
pub unsafe fn draw_tree(node: Type, width_spacing: usize, f: fn(Type) -> String) -> String {
    let mut column = 0;

    let mut prev_depth = None;
    let mut coordinates = BTreeMap::<Coordinate, Type>::new();
    let mut stack = vec![(0, node)];
    while let Some((depth, next)) = stack.pop() {
        let display = f(next);

        // Add width
        let width = display.chars().count();

        if let Some(pd) = prev_depth
            && depth <= pd
        {
            column += width_spacing + width + 1;
        }
        prev_depth = Some(depth);

        // Add coordinates of the node
        coordinates.insert(
            Coordinate {
                x: column,
                y: depth,
            },
            next,
        );

        // Add new nodes to stack.
        stack.extend(next.as_ref().next.iter().copied().map(|n| (depth + 1, n)));
    }

    let mut output = String::new();
    let mut row = 0;
    let mut column = 0;
    for (Coordinate { x, y }, node) in &coordinates {
        let row_diff = y - row;
        if row_diff > 0 {
            column = 0;

            let mut prev_iter = coordinates
                .range((
                    Included(Coordinate { x: 0, y: *y - 1 }),
                    Excluded(Coordinate { x: 0, y: *y }),
                ))
                .map(|(coord, _)| coord)
                .copied()
                .peekable();
            output.push('\n');
            let mut last = 0;
            while let Some(prev) = prev_iter.next() {
                let start = Coordinate { x: prev.x, y: *y };
                let end = match prev_iter.peek() {
                    Some(Coordinate { x, .. }) => Coordinate { x: *x, y: *y },
                    None => Coordinate { x: 0, y: *y + 1 },
                };

                let mut below_iter = coordinates
                    .range((Included(start), Excluded(end)))
                    .map(|(coord, _)| coord)
                    .copied()
                    .peekable();

                if let Some(first) = below_iter.next() {
                    output.extend(repeat(' ').take(prev.x - last));

                    if let Some(second) = below_iter.peek() {
                        debug_assert!(second.y == first.y);

                        output.push('├');
                        output.extend(repeat('─').take(second.x - first.x - 1));

                        while let Some(first_following) = below_iter.next() {
                            if let Some(second_following) = below_iter.peek() {
                                output.push('┬');
                                output.extend(
                                    repeat('─').take(second_following.x - first_following.x - 1),
                                );
                            } else {
                                output.push('┐');
                                last = first_following.x + 1;
                            }
                        }
                    } else {
                        output.push('│');
                        last = first.x + 1;
                    }
                }
            }
            output.push('\n');
        }
        row = *y;

        let column_diff = x - column;
        output.extend(repeat(' ').take(column_diff));
        column = *x;

        let display = f(*node);
        column += display.chars().count();
        output.push_str(&display);
    }
    output
}