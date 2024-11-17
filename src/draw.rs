use crate::verifier::*;
use std::cmp::Ordering;
use std::collections::BTreeMap;
use std::iter::repeat;
use std::ops::Bound::{Excluded, Included};

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

pub type Type = *mut VerifierNode;

/// Draws a tree.
pub unsafe fn draw_tree(node: Type, width_spacing: usize, f: fn(Type) -> String) -> String {
    let mut column = 0;

    let mut prev_depth = None;
    let mut coordinates = BTreeMap::<Coordinate, Type>::new();
    let mut stack = vec![(0, node)];
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    while let Some((depth, next)) = stack.pop() {
        debug_assert!(check.next().is_some());
        let display = f(next);

        // Add width
        let width = display.chars().count();

        // Only increment column when staying at same depth or going back up
        if let Some(pd) = prev_depth {
            if depth <= pd {
                column += width_spacing;
            }
        }

        // Store coordinates before adding width to maintain proper spacing
        coordinates.insert(
            Coordinate {
                x: column,
                y: depth,
            },
            next,
        );

        // Now increment column by width for next iteration
        column += width;
        prev_depth = Some(depth);

        // Add new nodes to stack
        if let crate::verifier::InnerNextVerifierNode::Branch(branch) = &next.as_ref().unwrap().next
        {
            stack.extend(branch.iter().copied().map(|n| (depth + 1, n)));
        }
    }

    let mut output = String::new();
    let mut row = 0;
    let mut column = 0;
    #[cfg(debug_assertions)]
    let mut check = (0..1000).into_iter();
    for (Coordinate { x, y }, node) in &coordinates {
        debug_assert!(check.next().is_some());
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

            #[cfg(debug_assertions)]
            let mut inner_check = (0..1000).into_iter();
            while let Some(prev) = prev_iter.next() {
                debug_assert!(inner_check.next().is_some());
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

                        #[cfg(debug_assertions)]
                        let mut inner_inner_check = (0..1000).into_iter();
                        while let Some(first_following) = below_iter.next() {
                            debug_assert!(inner_inner_check.next().is_some());
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
