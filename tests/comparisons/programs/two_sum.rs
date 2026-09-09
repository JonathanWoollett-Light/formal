fn main() {
    let nums = [2i32, 7, 11, 15];
    let target = 9i32;
    let cap = 8i32;
    let mut used = [0i32; 8];
    let mut keys = [0i32; 8];
    let mut vals = [0usize; 8];
    for i in 0..nums.len() {
        let c = target - nums[i];
        let mut h = (((c % cap) + cap) % cap) as usize;
        while used[h] != 0 {
            if keys[h] == c {
                println!("{} {}", vals[h], i);
                return;
            }
            h = (h + 1) % cap as usize;
        }
        h = (((nums[i] % cap) + cap) % cap) as usize;
        while used[h] != 0 {
            h = (h + 1) % cap as usize;
        }
        used[h] = 1;
        keys[h] = nums[i];
        vals[h] = i;
    }
}
