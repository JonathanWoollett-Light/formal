#include <iostream>
#include <vector>
#include <algorithm>
int main(int argc, char **argv){
    int n = argc>1 ? std::stoi(argv[1]) : 12;
    std::vector<int> perm(n), cnt(n, 0), work(n);
    for(int i=0;i<n;i++) perm[i]=i;
    int maxflips=0, parity=0; long checksum=0;
    for(;;){
        work = perm;
        int flips=0, k;
        while((k=work[0])!=0){
            std::reverse(work.begin(), work.begin()+k+1);
            flips++;
        }
        maxflips = std::max(maxflips, flips);
        checksum += parity ? -flips : flips;
        parity ^= 1;
        int i=1;
        for(; i<n; i++){
            int first=perm[0];
            for(int j=0;j<i;j++) perm[j]=perm[j+1];
            perm[i]=first;
            if(++cnt[i] <= i) break;
            cnt[i]=0;
        }
        if(i==n) break;
    }
    std::cout << checksum << "\nPfannkuchen(" << n << ") = " << maxflips << "\n";
}
