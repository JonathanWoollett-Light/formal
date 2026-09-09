#include <stdio.h>
int main(void){
    int coins[3] = {1,2,5}, amount = 11, dp[12];
    dp[0] = 0;
    for(int v=1;v<=amount;v++) dp[v] = 99;
    for(int c=0;c<3;c++)
        for(int v=coins[c];v<=amount;v++)
            if(dp[v-coins[c]]+1 < dp[v]) dp[v] = dp[v-coins[c]]+1;
    printf("%d\n", dp[amount]);
    return 0;
}
