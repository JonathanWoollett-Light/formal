const std = @import("std");
pub fn main() !void {
    var starts = [_]usize{ 2, 1, 15, 8 };
    var ends = [_]usize{ 6, 3, 18, 10 };
    var pass: usize = 0;
    var i: usize = 0;
    while (pass < starts.len) : (pass += 1) {
        i = 0;
        while (i + 1 < starts.len) : (i += 1) {
            if (starts[i] > starts[i + 1]) {
                std.mem.swap(usize, &starts[i], &starts[i + 1]);
                std.mem.swap(usize, &ends[i], &ends[i + 1]);
            }
        }
    }
    var outs: [4]usize = undefined;
    var oute: [4]usize = undefined;
    var n: usize = 0;
    var s: usize = starts[0];
    var e: usize = ends[0];
    i = 1;
    while (i < starts.len) : (i += 1) {
        if (starts[i] <= e) {
            if (ends[i] > e) e = ends[i];
        } else {
            outs[n] = s;
            oute[n] = e;
            n += 1;
            s = starts[i];
            e = ends[i];
        }
    }
    outs[n] = s;
    oute[n] = e;
    n += 1;
    const out = std.io.getStdOut().writer();
    i = 0;
    while (i < n) : (i += 1) try out.print("{d} {d}\n", .{ outs[i], oute[i] });
}
