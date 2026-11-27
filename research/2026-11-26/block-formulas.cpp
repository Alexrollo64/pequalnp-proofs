// Enumerate truth tables of minimum-size binary AND/OR trees on one copy.
// Usage: g++ -O3 -std=c++17 block-formulas.cpp -o block-formulas && ./block-formulas
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <unordered_map>
using Word = std::uint64_t;
constexpr Word target = 31917056;
std::unordered_map<Word, unsigned> cost;
std::array<std::vector<Word>, 8> level;

void record(Word x, int size) {
    if (cost.emplace(x, size).second) {
        level[size].push_back(x);
    }
}

std::string tree(Word x) {
    int n = cost.at(x);
    if (!n) {
        auto it = std::find(level[0].begin(), level[0].end(), x);
        return "v" + std::to_string(it-level[0].begin());
    }
    for (int i=0; i<n; ++i)
        for (Word a : level[i])
            for (Word b : level[n-1-i]) {
                if ((a & b) == x) return "(" + tree(a) + "&" + tree(b) + ")";
                if ((a | b) == x) return "(" + tree(a) + "|" + tree(b) + ")";
            }
    throw std::logic_error("missing predecessor");
}

int main() {
    for (int j=0; j<10; ++j) {
        Word x=0;
        for (int r=0; r<5; ++r)
            for (int c=0; c<5; ++c)
                if (j == r || j == 5+c) x |= 1U << (5*r+c);
        // Bits 25 through 34 represent the ten one-sided inputs.
        x |= Word{1} << (25+j);
        record(x, 0);
    }
    for (int n=1; n<=7; ++n)
        for (int i=0; i<=(n-1)/2; ++i)
            for (Word a : level[i])
                for (Word b : level[n-1-i]) {
                    record(a & b, n);
                    record(a | b, n);
                }
    for (int n=0; n<=7; ++n) std::cerr << n << " " << level[n].size() << "\n";
    for (int j=0; j<25; ++j) {
        Word x = target ^ (1U << j);
        if (cost.count(x))
            std::cout << j << " " << int(cost[x]) << " " << tree(x) << "\n";
    }
}
