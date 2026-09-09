#include <iostream>
#include <vector>
int main(){
    std::vector<int> grid(20, 0);
    for(int cell : {0, 1, 5, 6, 12, 18, 19}) grid[cell] = 1;
    std::vector<int> stack(20);
    int cols=5, depth=0, islands=0;
    auto visit = [&](int cell){ if(grid[cell]){ grid[cell]=0; stack[depth++]=cell; } };
    for(int start=0;start<20;start++){
        if(!grid[start]) continue;
        islands++;
        visit(start);
        while(depth>0){
            int cell=stack[--depth], col=cell%cols;
            if(cell>=cols) visit(cell-cols);
            if(cell+cols<20) visit(cell+cols);
            if(col!=0) visit(cell-1);
            if(col+1!=cols) visit(cell+1);
        }
    }
    std::cout << islands << "\n";
}
