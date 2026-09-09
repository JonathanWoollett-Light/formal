#include <stdio.h>
int main(void){
    int nums[4] = {2,7,11,15};
    int target = 9, cap = 8;
    int used[8] = {0}, keys[8] = {0}, vals[8] = {0};
    for(int i=0;i<4;i++){
        int c = target - nums[i];
        int h = ((c % cap) + cap) % cap;
        while(used[h]){
            if(keys[h] == c){ printf("%d %d\n", vals[h], i); return 0; }
            h = (h + 1) % cap;
        }
        h = ((nums[i] % cap) + cap) % cap;
        while(used[h]) h = (h + 1) % cap;
        used[h] = 1; keys[h] = nums[i]; vals[h] = i;
    }
    return 0;
}
