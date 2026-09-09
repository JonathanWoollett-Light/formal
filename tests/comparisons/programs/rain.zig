const std = @import("std");
pub fn main() !void {
    const h = [_]usize{ 0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1 };
    var left: usize = 0;
    var right: usize = h.len - 1;
    var lmax: usize = 0;
    var rmax: usize = 0;
    var water: usize = 0;
    while (left < right) {
        if (h[left] < h[right]) {
            if (h[left] >= lmax) { lmax = h[left]; } else { water += lmax - h[left]; }
            left += 1;
        } else {
            if (h[right] >= rmax) { rmax = h[right]; } else { water += rmax - h[right]; }
            right -= 1;
        }
    }
    const out = std.io.getStdOut().writer();
    try out.print("{d}\n", .{water});
}
