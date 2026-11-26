#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <vector>
#include <random>
struct Gate { uint32_t left, right, value; bool disjunction; };
int main(int argc, char** argv) {
  if (argc < 6) return 2;
  int count = std::atoi(argv[1]), bits = std::atoi(argv[2]);
  int budget = std::atoi(argv[3]), seeds = std::atoi(argv[4]);
  uint32_t target = std::strtoul(argv[5], nullptr, 10), space = 1u << bits;
  if (argc != 6 + count || bits > 21) return 2;
  std::vector<uint32_t> primary(count);
  for (int i = 0; i < count; i++) primary[i] = std::strtoul(argv[6+i], nullptr, 10);
  std::vector<int> seen(space, -1), wire(space);
  std::vector<Gate> parent(space);
  int version = 0;
  auto solve = [&](const std::vector<Gate>& initial) {
    version++;
    int limit = budget - initial.size();
    std::vector<std::vector<uint32_t>> layers(limit + 1);
    auto put = [&](uint32_t value, int cost, int index, Gate gate) {
      if (seen[value] == version) return;
      seen[value] = version; wire[value] = index; parent[value] = gate;
      layers[cost].push_back(value);
    };
    for (int i = 0; i < count; i++) put(primary[i], 0, i, {});
    for (auto gate : initial) put(gate.value, 0, -1, gate);
    for (int cost = 1; cost <= limit && seen[target] != version; cost++) {
      for (int i = 0; i <= cost-1-i && seen[target] != version; i++) {
        for (auto a : layers[i]) {
          for (auto b : layers[cost-1-i]) {
            if (i == cost-1-i && a >= b) continue;
            put(a & b, cost, -1, {a,b,a&b,false});
            put(a | b, cost, -1, {a,b,a|b,true});
          }
          if (seen[target] == version) break;
        }
      }
    }
    if (seen[target] != version) return false;
    int next = count;
    auto emit = [&](auto&& self, uint32_t value) -> int {
      if (wire[value] >= 0) return wire[value];
      auto gate = parent[value];
      int a = self(self, gate.left), b = self(self, gate.right);
      int index = wire[value] = next++;
      std::cout << index << " " << (gate.disjunction ? "or" : "and") << " " << a << " " << b << "\n";
      return index;
    };
    int output = emit(emit,target);
    std::cout << "out " << output << "\n";
    return true;
  };
  std::vector<Gate> candidates;
  for (int i=0; i<count; i++) for (int j=i+1; j<count; j++) {
    for (bool disjunction : {false,true}) {
      auto a=primary[i],b=primary[j],v=disjunction ? a|b : a&b;
      if (v && v != space-1 && std::find(primary.begin(),primary.end(),v)==primary.end())
        candidates.push_back({a,b,v,disjunction});
    }
  }
  if (seeds >= 3) {
    std::vector<int> cost(space,-1);
    std::vector<Gate> source(space);
    std::vector<std::vector<uint32_t>> levels(4);
    for (auto value : primary) { cost[value]=0; levels[0].push_back(value); }
    for (int k=1;k<=3;k++) {
      for (int i=0;i<k;i++) for (auto a:levels[i]) for (auto b:levels[k-1-i]) {
        for (bool disjunction : {false,true}) {
          auto value=disjunction ? a|b : a&b;
          if (cost[value] >= 0 || value==0 || value==space-1) continue;
          cost[value]=k;source[value]={a,b,value,disjunction};levels[k].push_back(value);
        }
      }
    }
    if (seeds >= 4) {
      std::vector<uint32_t> pool=levels[1];
      pool.insert(pool.end(),levels[2].begin(),levels[2].end());
      std::vector<std::pair<size_t,size_t>> pairs;
      for (size_t a=0;a<pool.size();a++) for(size_t b=a+1;b<pool.size();b++) pairs.push_back({a,b});
      std::mt19937 random(target);
      std::shuffle(pairs.begin(),pairs.end(),random);
      std::cerr << "two-support candidates " << pairs.size() << " quota 5000\n";
      size_t tried=0;
      for (auto pair:pairs) {
        std::vector<Gate> initial;
        std::vector<uint32_t> done=primary;
        auto collect=[&](auto&& self,uint32_t v)->void {
          if(std::find(done.begin(),done.end(),v)!=done.end()) return;
          auto gate=source[v];self(self,gate.left);self(self,gate.right);
          done.push_back(v);initial.push_back(gate);
        };
        collect(collect,pool[pair.first]);collect(collect,pool[pair.second]);
        if (solve(initial)) return 0;
        tried++;
        if (tried%100==0) std::cerr << "tested " << tried << "\n";
        if (tried>=5000) break;
      }
      return 1;
    }
    for (int k=2;k<=3;k++) {
      std::cerr << "support cost " << k << " candidates " << levels[k].size() << "\n";
      for (auto value : levels[k]) {
        std::vector<Gate> initial;
        std::vector<uint32_t> done=primary;
        auto collect=[&](auto&& self,uint32_t v)->void {
          if (std::find(done.begin(),done.end(),v)!=done.end()) return;
          auto gate=source[v];self(self,gate.left);self(self,gate.right);
          done.push_back(v);initial.push_back(gate);
        };
        collect(collect,value);
        if (solve(initial)) return 0;
      }
    }
  }
  if (solve({})) return 0;
  for (auto gate : candidates) if (solve({gate})) return 0;
  if (seeds >= 2) for (size_t i=0; i<candidates.size(); i++) {
    auto first=candidates[i];
    for (size_t j=i+1; j<candidates.size(); j++)
      if (first.value!=candidates[j].value && solve({first,candidates[j]})) return 0;
    for (auto a : primary) for (bool disjunction : {false,true}) {
      auto value=disjunction ? first.value|a : first.value&a;
      if (value && value!=space-1 && value!=a && value!=first.value &&
          std::find(primary.begin(),primary.end(),value)==primary.end() &&
          solve({first,{first.value,a,value,disjunction}})) return 0;
    }
  }
  return 1;
}
