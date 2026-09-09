fn main() {
    let h: [u32; 12] = [0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1];
    let mut left = 0usize;
    let mut right = h.len() - 1;
    let mut lmax = 0u32;
    let mut rmax = 0u32;
    let mut water = 0u32;
    while left < right {
        if h[left] < h[right] {
            if h[left] >= lmax { lmax = h[left]; } else { water += lmax - h[left]; }
            left += 1;
        } else {
            if h[right] >= rmax { rmax = h[right]; } else { water += rmax - h[right]; }
            right -= 1;
        }
    }
    println!("{}", water);
}
