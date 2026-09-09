#include <iostream>
#include <vector>
int main(){
    std::vector<int> starts = {2, 1, 15, 8}, ends = {6, 3, 18, 10};
    int n = 4;
    for(int pass=0;pass<n;pass++)
        for(int i=0;i+1<n;i++)
            if(starts[i]>starts[i+1]){
                std::swap(starts[i], starts[i+1]);
                std::swap(ends[i], ends[i+1]);
            }
    int start=starts[0], end=ends[0];
    for(int i=1;i<n;i++){
        if(starts[i]<=end){
            if(ends[i]>end) end=ends[i];
        } else {
            std::cout << start << " " << end << "\n";
            start=starts[i]; end=ends[i];
        }
    }
    std::cout << start << " " << end << "\n";
}
