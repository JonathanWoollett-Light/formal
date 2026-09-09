const std = @import("std");
pub fn main() !void {
    const nums = [_]i32{ 2, 7, 11, 15 };
    const target: i32 = 9;
    const cap: i32 = 8;
    var used = [_]i32{0} ** 8;
    var keys = [_]i32{0} ** 8;
    var vals = [_]usize{0} ** 8;
    const out = std.io.getStdOut().writer();
    var i: usize = 0;
    while (i < nums.len) : (i += 1) {
        const c = target - nums[i];
        var h: usize = @intCast(@mod(c, cap));
        while (used[h] != 0) {
            if (keys[h] == c) {
                try out.print("{d} {d}\n", .{ vals[h], i });
                return;
            }
            h = (h + 1) % @as(usize, @intCast(cap));
        }
        h = @intCast(@mod(nums[i], cap));
        while (used[h] != 0) {
            h = (h + 1) % @as(usize, @intCast(cap));
        }
        used[h] = 1;
        keys[h] = nums[i];
        vals[h] = i;
    }
}
