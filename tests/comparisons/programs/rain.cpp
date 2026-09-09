#include <iostream>
#include <vector>
int main(){
    std::vector<int> h = {0, 1, 0, 2, 1, 0, 1, 3, 2, 1, 2, 1};
    int left=0, right=11, lmax=0, rmax=0, water=0;
    while(left<right){
        if(h[left]<h[right]){
            if(h[left]>=lmax) lmax=h[left];
            else water += lmax-h[left];
            left++;
        } else {
            if(h[right]>=rmax) rmax=h[right];
            else water += rmax-h[right];
            right--;
        }
    }
    std::cout << water << "\n";
}
