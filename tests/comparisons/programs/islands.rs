fn visit(cell: usize, grid: &mut [u32], stack: &mut [usize], depth: &mut usize) {
    if grid[cell] != 0 {
        grid[cell] = 0;
        stack[*depth] = cell;
        *depth += 1;
    }
}

fn main() {
    let cols = 5usize;
    let mut grid: [u32; 20] = [
        1, 1, 0, 0, 0,
        1, 1, 0, 0, 0,
        0, 0, 1, 0, 0,
        0, 0, 0, 1, 1,
    ];
    let cells = grid.len();
    let mut stack = [0usize; 20];
    let mut depth = 0usize;
    let mut islands = 0u32;
    for start in 0..cells {
        if grid[start] == 0 { continue; }
        islands += 1;
        grid[start] = 0;
        stack[depth] = start;
        depth += 1;
        while depth != 0 {
            depth -= 1;
            let cell = stack[depth];
            let col = cell % cols;
            if cell >= cols { visit(cell - cols, &mut grid, &mut stack, &mut depth); }
            if cell + cols < cells { visit(cell + cols, &mut grid, &mut stack, &mut depth); }
            if col != 0 { visit(cell - 1, &mut grid, &mut stack, &mut depth); }
            if col + 1 != cols { visit(cell + 1, &mut grid, &mut stack, &mut depth); }
        }
    }
    println!("{}", islands);
}
