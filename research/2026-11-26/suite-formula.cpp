// Exact AND/OR formula synthesis on the selected 18 inputs, using subset convolutions.
#include <array>
#include <cstdint>
#include <iostream>
#include <fstream>
#include <stdexcept>
#include <string>
#include <vector>

using Counts = std::vector<std::int64_t>;
constexpr int width = 18, size = 1 << width;
constexpr std::array<int,width> cases = {20,34,44,75,89,99,31,32,33,86,87,88,41,96,40,91,25,76};
std::vector<int> costs(size,-1), leaf(size,-1);
std::vector<std::vector<int>> levels;
std::vector<Counts> subsets, supersets;

void transform(Counts& counts, bool upwards, bool inverse) {
    int sign = inverse ? -1 : 1;
    for (int step=1; step<size; step*=2)
        for (int start=0; start<size; start+=2*step)
            for (int p=start; p<start+step; ++p) {
                if (upwards) counts[p+step] += sign*counts[p];
                else counts[p] += sign*counts[p+step];
            }
}

std::string formula(int x) {
    if (costs[x]==0) return "v"+std::to_string(leaf[x]);
    for (int i=0; i<costs[x]; ++i) {
        int j=costs[x]-1-i;
        for (bool use_or : {true,false}) {
            auto fits=[&](int y) {return use_or ? (x|y)==x : (x&y)==x;};
            std::vector<int> right;
            for(int b : levels[j]) if (fits(b)) right.push_back(b);
            for(int a : levels[i]) if (fits(a)) for(int b : right)
                if ((use_or ? a|b : a&b)==x)
                    return "("+formula(a)+(use_or?"|":"&")+formula(b)+")";
        }
    }
    throw std::logic_error("missing witness");
}

int main(int argc, char** argv) {
    int target=0;
    for(int j=0;j<20;++j) {
        int x=0;
        for(int i=0;i<width;++i) {
            int r=cases[i]/10,c=cases[i]%10;
            if(j==r || j==10+c) x|=1<<i;
            if(r/5==c/5 && ((31917056>>(5*(r%5)+c%5))&1)) target|=1<<i;
        }
        leaf[x]=j;
    }
    for(int n=0;n<=17;++n) {
        Counts u(size),v(size);
        if(n>0) {
            // Invert the zeta-transformed pair counts, separately for union and intersection.
            for(int i=0;i<=(n-1)/2;++i) for(int x=0;x<size;++x) {
                u[x]+=subsets[i][x]*subsets[n-1-i][x];
                v[x]+=supersets[i][x]*supersets[n-1-i][x];
            }
            transform(u,true,true); transform(v,false,true);
        }
        levels.emplace_back();
        for(int x=0;x<size;++x) {
            bool new_mask=costs[x]<0 && (n==0 ? leaf[x]>=0 : u[x]+v[x]>0);
            if(new_mask) {costs[x]=n;levels.back().push_back(x);}
            u[x]=v[x]=new_mask;
        }
        std::cout<<n<<" "<<levels[n].size()<<"\n";
        if(costs[target]>=0) {
            if(argc==2) {std::ofstream out(argv[1],std::ios::binary); for(int c : costs) out.put(static_cast<char>(c));}
            std::cout<<formula(target)<<"\n";return 0;}
        transform(u,true,false);transform(v,false,false);
        subsets.push_back(std::move(u)); supersets.push_back(std::move(v));
    }
    return 1;
}
