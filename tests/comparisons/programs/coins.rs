fn main() {
    let coins: [usize; 3] = [1, 2, 5];
    let amount = 11usize;
    // 99 stands in for "no way to make this amount"
    let mut dp = [99u32; 12];
    dp[0] = 0;
    for c in coins.iter() {
        for v in *c..=amount {
            let candidate = dp[v - c] + 1;
            if candidate < dp[v] { dp[v] = candidate; }
        }
    }
    println!("{}", dp[amount]);
}
