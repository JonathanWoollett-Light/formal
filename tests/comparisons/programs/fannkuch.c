#include <stdio.h>
#include <stdlib.h>
#include <string.h>
int main(int argc, char **argv){
    int n = argc>1 ? atoi(argv[1]) : 12;
    int perm[32], cnt[32], work[32];
    for(int i=0;i<n;i++){ perm[i]=i; cnt[i]=0; }
    int maxflips=0, parity=0; long checksum=0;
    for(;;){
        memcpy(work, perm, n*sizeof(int));
        int flips=0, k;
        while((k=work[0])!=0){
            for(int i=0,j=k;i<j;i++,j--){ int t=work[i]; work[i]=work[j]; work[j]=t; }
            flips++;
        }
        if(flips>maxflips) maxflips=flips;
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
    printf("%ld\nPfannkuchen(%d) = %d\n", checksum, n, maxflips);
    return 0;
}
