#include <iostream>
#include <vector>
int main(){
    std::vector<int> nums = {2, 7, 11, 15};
    int n = 4, target = 9, a = 0, b = 0;
    for(int i=0;i<n;i++)
        for(int j=i+1;j<n;j++)
            if(nums[i]+nums[j]==target){ a=i; b=j; }
    std::cout << a << " " << b << "\n";
}
