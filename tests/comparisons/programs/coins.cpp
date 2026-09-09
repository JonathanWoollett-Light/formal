#include <iostream>
#include <vector>
int main(){
    std::vector<int> coins = {1, 2, 5};
    int amount = 11;
    std::vector<int> dp(amount+1, 99);
    dp[0] = 0;
    for(int c : coins)
        for(int v=c;v<=amount;v++)
            if(dp[v-c]+1 < dp[v]) dp[v] = dp[v-c]+1;
    std::cout << dp[amount] << "\n";
}
