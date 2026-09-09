const std = @import("std");
pub fn main() !void {
    const coins = [_]usize{ 1, 2, 5 };
    const amount: usize = 11;
    var dp: [12]usize = undefined;
    dp[0] = 0;
    var v: usize = 1;
    while (v <= amount) : (v += 1) dp[v] = 99;
    var c: usize = 0;
    while (c < coins.len) : (c += 1) {
        v = coins[c];
        while (v <= amount) : (v += 1) {
            const candidate = dp[v - coins[c]] + 1;
            if (candidate < dp[v]) dp[v] = candidate;
        }
    }
    const out = std.io.getStdOut().writer();
    try out.print("{d}\n", .{dp[amount]});
}
