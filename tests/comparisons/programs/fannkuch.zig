const std = @import("std");
pub fn main() !void {
    const n: usize = 12;
    var perm: [32]usize = undefined;
    var cnt: [32]usize = undefined;
    var work: [32]usize = undefined;
    var i: usize = 0;
    while (i < n) : (i += 1) { perm[i] = i; cnt[i] = 0; }
    var maxflips: usize = 0;
    var checksum: i64 = 0;
    var parity: u1 = 0;
    while (true) {
        std.mem.copyForwards(usize, work[0..n], perm[0..n]);
        var flips: usize = 0;
        while (work[0] != 0) {
            const k = work[0];
            std.mem.reverse(usize, work[0 .. k + 1]);
            flips += 1;
        }
        if (flips > maxflips) maxflips = flips;
        if (parity == 0) { checksum += @intCast(flips); } else { checksum -= @intCast(flips); }
        parity ^= 1;
        i = 1;
        while (i < n) : (i += 1) {
            const first = perm[0];
            var j: usize = 0;
            while (j < i) : (j += 1) perm[j] = perm[j + 1];
            perm[i] = first;
            cnt[i] += 1;
            if (cnt[i] <= i) break;
            cnt[i] = 0;
        }
        if (i == n) break;
    }
    const out = std.io.getStdOut().writer();
    try out.print("{d}\nPfannkuchen({d}) = {d}\n", .{ checksum, n, maxflips });
}
