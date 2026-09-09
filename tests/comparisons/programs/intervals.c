#include <stdio.h>
int main(void){
    int starts[4] = {2,1,15,8}, ends[4] = {6,3,18,10}, n = 4;
    for(int pass=0;pass<n;pass++)
        for(int i=0;i<n-1;i++)
            if(starts[i]>starts[i+1]){
                int t = starts[i]; starts[i] = starts[i+1]; starts[i+1] = t;
                t = ends[i]; ends[i] = ends[i+1]; ends[i+1] = t;
            }
    int outs[4], oute[4], m = 0, s = starts[0], e = ends[0];
    for(int i=1;i<n;i++){
        if(starts[i]<=e){
            if(ends[i]>e) e = ends[i];
        }else{
            outs[m] = s; oute[m] = e; m++;
            s = starts[i]; e = ends[i];
        }
    }
    outs[m] = s; oute[m] = e; m++;
    for(int i=0;i<m;i++) printf("%d %d\n", outs[i], oute[i]);
    return 0;
}
