fn main() {
    let mut starts: [u32; 4] = [2, 1, 15, 8];
    let mut ends: [u32; 4] = [6, 3, 18, 10];
    let n = starts.len();
    for _ in 0..n {
        for j in 0..n - 1 {
            if starts[j] > starts[j + 1] {
                starts.swap(j, j + 1);
                ends.swap(j, j + 1);
            }
        }
    }
    let mut outs = [0u32; 4];
    let mut oute = [0u32; 4];
    let mut count = 0usize;
    let mut start = starts[0];
    let mut end = ends[0];
    for i in 1..n {
        if starts[i] <= end {
            if ends[i] > end { end = ends[i]; }
        } else {
            outs[count] = start;
            oute[count] = end;
            count += 1;
            start = starts[i];
            end = ends[i];
        }
    }
    outs[count] = start;
    oute[count] = end;
    count += 1;
    for i in 0..count {
        println!("{} {}", outs[i], oute[i]);
    }
}
