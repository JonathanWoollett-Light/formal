fn main() {
    let n: usize = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(12);
    let mut perm: Vec<usize> = (0..n).collect();
    let mut cnt = vec![0usize; n];
    let mut work = vec![0usize; n];
    let mut maxflips = 0usize;
    let mut checksum: i64 = 0;
    let mut parity = 0u8;
    loop {
        work.copy_from_slice(&perm);
        let mut flips = 0usize;
        while work[0] != 0 {
            let k = work[0];
            work[0..=k].reverse();
            flips += 1;
        }
        if flips > maxflips { maxflips = flips; }
        checksum += if parity == 0 { flips as i64 } else { -(flips as i64) };
        parity ^= 1;
        let mut i = 1;
        while i < n {
            let first = perm[0];
            for j in 0..i { perm[j] = perm[j + 1]; }
            perm[i] = first;
            cnt[i] += 1;
            if cnt[i] <= i { break; }
            cnt[i] = 0;
            i += 1;
        }
        if i == n { break; }
    }
    println!("{}\nPfannkuchen({}) = {}", checksum, n, maxflips);
}
