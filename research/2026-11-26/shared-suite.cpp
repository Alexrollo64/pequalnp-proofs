// Exact AND/OR formula synthesis on the selected 18 inputs, using subset convolutions.
#include <array>
#include <map>
#include <set>
#include <iomanip>
#include <cstdint>
#include <iostream>
#include <tuple>
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

using Word = __uint128_t;
std::map<int,std::set<Word>> memo;
std::map<int,std::set<Word>> raw;
std::map<std::pair<int,Word>,int> inputNames;
Word cell(int p) {return Word{1} << p;}
int weight(Word x) {
    return __builtin_popcountll(static_cast<std::uint64_t>(x)) +
           __builtin_popcountll(static_cast<std::uint64_t>(x >> 64));
}

// Unordered splits of a minimum formula with projected truth table x.
using Split = std::tuple<bool,int,int>;
std::vector<Split> splits(int x) {
    std::vector<Split> answer;
    for (int i=0; i<=(costs[x]-1)/2; ++i) {
        int j=costs[x]-1-i;
        for (bool use_or : {true,false}) {
            auto fits=[&](int y) {return use_or ? (x|y)==x : (x&y)==x;};
            std::vector<int> right;
            for (int b : levels[j]) if (fits(b)) right.push_back(b);
            for (int a : levels[i]) {
                if (!fits(a)) continue;
                for (int b : right) {
                    if (i==j && a>b) continue;
                    if ((use_or ? (a|b) : (a&b))==x) answer.emplace_back(use_or,a,b);
                }
            }
        }
    }
    return answer;
}

// Every subtree of a minimum formula has minimum cost on the suite.
// Keep all truth tables, including distinct raw wires that agree on the suite.
const std::set<Word>& lift(int x) {
    auto [it,added]=memo.try_emplace(x);
    auto& result=it->second;
    if (!added) return result;
    if (costs[x]==0) {
        result=raw.at(x);
        return result;
    }
    for (auto [use_or,a,b] : splits(x)) {
        const auto& left=lift(a);
        const auto& right=lift(b);
        for (Word l : left) for (Word r : right) result.insert(use_or ? (l|r) : (l&r));
    }
    return result;
}

std::string witness(int x, Word actual) {
    if (costs[x]==0) return "v"+std::to_string(inputNames.at({x,actual}));
    for (auto [use_or,a,b] : splits(x)) {
        for (Word l : lift(a)) for (Word r : lift(b)) {
            if ((use_or ? (l|r) : (l&r))==actual)
                return "("+witness(a,l)+(use_or?"|":"&")+witness(b,r)+")";
        }
    }
    throw std::logic_error("missing witness");
}

int main(int argc, char** argv) {
    if (argc!=3 && argc!=4) {
        std::cerr<<"usage: shared-suite LEFT RIGHT [error-mask-hex]\n";return 2;
    }
    Word target100=0; std::array<Word,20> all{}; int target=0; std::array<int,20> masks{};
    for(int j=0;j<20;++j) {
        int x=0;
        for(int i=0;i<width;++i) {
            int r=cases[i]/10,c=cases[i]%10;
            if(j==r || j==10+c) x|=1<<i;
            if(r/5==c/5 && ((31917056>>(5*(r%5)+c%5))&1)) target|=1<<i;
        }
        leaf[x]=j; masks[j]=x;
        for (int p=0;p<100;++p) {
            int r=p/10,c=p%10;
            if(j==r || j==10+c) all[j]|=cell(p);
            if(r/5==c/5 && ((31917056>>(5*(r%5)+c%5))&1)) target100|=cell(p);
        }
        raw[x].insert(all[j]); inputNames[{x,all[j]}]=j;
    }

    int a=std::stoi(argv[1]), b=std::stoi(argv[2]);
    int projected=masks.at(a)|masks.at(b);
    Word full=all.at(a)|all.at(b);
    leaf[projected]=20;
    raw[projected].insert(full);
    inputNames[{projected,full}]=20;
    for(int n=0;n<=15;++n) {
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

        if(costs[target]>=0) {
            const auto& tables=lift(target);
            if(argc==4) {
                Word error=0;
                std::string hex=argv[3];
                if(hex.empty() || hex.size()>25) return 2;
                for(char ch : hex) {
                    int digit=ch>='0' && ch<='9' ? ch-'0' : ch-'a'+10;
                    if(!((ch>='0' && ch<='9') || (ch>='a' && ch<='f'))) return 2;
                    error=16*error+digit;
                }
                if(!tables.count(error^target100)) return 3;
                std::cout<<witness(target,error^target100)<<"\n";
                return 0;
            }
            std::cout<<"tail "<<n<<"\n";
            for (Word t : tables) {
                Word e=t^target100;
                std::cout << weight(e) << " " << std::hex << static_cast<std::uint64_t>(e>>64)
                    << std::setw(16) << std::setfill('0') << static_cast<std::uint64_t>(e) << std::dec << "\n";
            }
            return 0;
        }

        transform(u,true,false);transform(v,false,false);
        subsets.push_back(std::move(u)); supersets.push_back(std::move(v));
    }
    std::cout<<"no tail of at most 15 gates\n";
    return 1;
}
