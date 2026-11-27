// Independently verify the Bellman equations of a complete table of formula costs.
// On a target t, AND is union on complemented masks. For OR, after choosing a
// submask a of t the other operand b may be any mask between t minus a and t.
#include <algorithm>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <vector>

int main(int argc, char** argv) {
    if(argc!=2) return 2;
    constexpr int width=18, count=1<<width, full=count-1;
    std::ifstream input(argv[1],std::ios::binary);
    std::vector<unsigned char> cost(count),best(count,255),mins(count);
    if(!input.read(reinterpret_cast<char*>(cost.data()),count) || input.peek()!=EOF) return 2;
    int cases[width]={20,34,44,75,89,99,31,32,33,86,87,88,41,96,40,91,25,76};
    for(int j=0;j<20;++j) {
        int mask=0;
        for(int i=0;i<width;++i)
            if(j==cases[i]/10 || j==10+cases[i]%10) mask|=1<<i;
        best[mask]=0;
    }
    std::vector<int> index(count);
    for(int flip : {0, full}) for(int t=0;t<count;++t) {
        int n=1;
        index[0]=0;
        for(int bits=t;bits;bits&=bits-1) {
            int bit=bits & -bits;
            for(int a=0;a<n;++a) index[n+a]=index[a]|bit;
            n*=2;
        }
        for(int a=0;a<n;++a) mins[a]=cost[index[a]^flip];
        for(int step=1;step<n;step*=2)
            for(int start=0;start<n;start+=2*step)
                for(int a=start;a<start+step;++a)
                    mins[a]=std::min(mins[a],mins[a+step]);
        int value=best[t^flip];
        for(int a=0;a<n;++a)
            value=std::min(value,1+cost[index[a]^flip]+mins[(n-1)^a]);
        best[t^flip]=value;
    }
    if(cost!=best) {std::cerr<<"Invalid cost certificate\n";return 1;}
    std::cout<<"Verified all 262144 costs against every possible root split.\n";
}
