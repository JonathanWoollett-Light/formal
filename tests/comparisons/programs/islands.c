#include <stdio.h>
int main(void){
    int grid[20] = {
        1,1,0,0,0,
        1,1,0,0,0,
        0,0,1,0,0,
        0,0,0,1,1,
    };
    int cells = 20, cols = 5, stack[20], top = 0, islands = 0;
    for(int start=0;start<cells;start++){
        if(!grid[start]) continue;
        islands++;
        grid[start] = 0; stack[top++] = start;
        while(top>0){
            int cell = stack[--top], col = cell%cols;
            if(cell>=cols && grid[cell-cols]){ grid[cell-cols]=0; stack[top++]=cell-cols; }
            if(cell+cols<cells && grid[cell+cols]){ grid[cell+cols]=0; stack[top++]=cell+cols; }
            if(col!=0 && grid[cell-1]){ grid[cell-1]=0; stack[top++]=cell-1; }
            if(col+1!=cols && grid[cell+1]){ grid[cell+1]=0; stack[top++]=cell+1; }
        }
    }
    printf("%d\n", islands);
    return 0;
}
