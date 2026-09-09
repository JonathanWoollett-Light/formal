fn main() {
    let nums: [u32; 4] = [2, 7, 11, 15];
    let target: u32 = 9;
    let mut a = 0usize;
    let mut b = 0usize;
    for i in 0..nums.len() {
        for j in i + 1..nums.len() {
            if nums[i] + nums[j] == target {
                a = i;
                b = j;
            }
        }
    }
    println!("{} {}", a, b);
}
