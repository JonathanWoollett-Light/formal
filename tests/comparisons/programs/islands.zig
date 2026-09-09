const std = @import("std");
pub fn main() !void {
    const cols: usize = 5;
    var grid = [_]u8{
        1, 1, 0, 0, 0,
        1, 1, 0, 0, 0,
        0, 0, 1, 0, 0,
        0, 0, 0, 1, 1,
    };
    var stack: [20]usize = undefined;
    var depth: usize = 0;
    var count: usize = 0;
    var start: usize = 0;
    while (start < grid.len) : (start += 1) {
        if (grid[start] == 0) continue;
        count += 1;
        grid[start] = 0;
        stack[depth] = start;
        depth += 1;
        while (depth != 0) {
            depth -= 1;
            const cell = stack[depth];
            const col = cell % cols;
            var nbr: [4]usize = undefined;
            var n: usize = 0;
            if (cell >= cols) { nbr[n] = cell - cols; n += 1; }
            if (cell + cols < grid.len) { nbr[n] = cell + cols; n += 1; }
            if (col != 0) { nbr[n] = cell - 1; n += 1; }
            if (col + 1 != cols) { nbr[n] = cell + 1; n += 1; }
            var k: usize = 0;
            while (k < n) : (k += 1) {
                if (grid[nbr[k]] == 0) continue;
                grid[nbr[k]] = 0;
                stack[depth] = nbr[k];
                depth += 1;
            }
        }
    }
    const out = std.io.getStdOut().writer();
    try out.print("{d}\n", .{count});
}
