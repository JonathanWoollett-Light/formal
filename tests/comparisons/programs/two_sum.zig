const std = @import("std");
pub fn main() !void {
    const nums = [_]usize{ 2, 7, 11, 15 };
    const target: usize = 9;
    var ans_i: usize = 0;
    var ans_j: usize = 0;
    var i: usize = 0;
    while (i < nums.len) : (i += 1) {
        var j: usize = i + 1;
        while (j < nums.len) : (j += 1) {
            if (nums[i] + nums[j] == target) { ans_i = i; ans_j = j; }
        }
    }
    const out = std.io.getStdOut().writer();
    try out.print("{d} {d}\n", .{ ans_i, ans_j });
}
