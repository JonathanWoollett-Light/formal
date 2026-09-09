#include <stdio.h>
int main(void){
    int nums[4] = {2,7,11,15}, target = 9, n = 4;
    int a = 0, b = 0;
    for(int i=0;i<n;i++)
        for(int j=i+1;j<n;j++)
            if(nums[i]+nums[j]==target){ a=i; b=j; }
    printf("%d %d\n", a, b);
    return 0;
}
