// Enumerate supports of one monotone Boolean signal with exclusive raw inputs.
#include <array>
#include <iostream>
#include <vector>
using namespace std;
constexpr array<int,16> wires={2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19};
constexpr array<int,7> sample={20,21,31,34,40,41,44};
int main() {
    array<unsigned,100> inputs{};
    vector<int> pos,neg;
    for(int p=0;p<100;++p) {
        int r=p/10,c=p%10;
        for(unsigned j=0;j<wires.size();++j)
            if(wires[j]==r || wires[j]==10+c) inputs[p]|=1u<<j;
        bool target=(r/5==c/5) && ((31917056>>(5*(r%5)+c%5))&1);
        (target ? pos : neg).push_back(p);
    }
    cout<<"mask,size,active_in_both_possible\n";
    for(unsigned s=0;s<(1u<<16);++s) {
        array<bool,100> on{},off{};
        for(int p : pos) for(int n : neg)
            if(!(inputs[p] & ~inputs[n] & ~s)) {on[p]=true;off[n]=true;}
        auto can_be_true=[&](int p) {
            for(int n : neg) if(off[n] && !(inputs[p] & ~inputs[n] & s)) return false;
            return true;
        };
        bool valid=true;
        for(int p : pos) if(on[p] && !can_be_true(p)) {valid=false;break;}
        if(!valid) continue;
        bool both=true;
        for(int offset : {0,55}) {
            bool block=false;
            for(int i : sample) if(can_be_true(i+offset)) block=true;
            both &= block;
        }
        cout<<s<<','<<__builtin_popcount(s)<<','<<both<<'\n';
    }
}
