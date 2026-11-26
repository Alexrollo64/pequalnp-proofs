#include <algorithm>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <map>
#include <vector>
using Mask = uint32_t;
struct Node { int op = -2; Mask left = 0, right = 0; int wire = -1; };
int main(int argc,char** argv) {
  if(argc!=6) return 2;
  int rows=std::atoi(argv[1]),cols=std::atoi(argv[2]),limit=std::atoi(argv[4]);
  bool allowNot=std::atoi(argv[5])!=0;
  if(rows<1||cols<1||rows*cols>25||limit<0||limit>20) return 2;
  size_t count=size_t(1)<<(rows*cols);
  Mask full=count-1,target=std::strtoul(argv[3],nullptr,10);
  if(target>=count) return 2;
  std::vector<Node> nodes(count);
  std::vector<std::vector<Mask>> layers(limit+1);
  for(int i=0;i<rows+cols;i++) {
    Mask mask=0;
    for(int r=0;r<rows;r++) for(int c=0;c<cols;c++)
      if(i==r||i==rows+c) mask |= Mask(1)<<(r*cols+c);
    if(nodes[mask].op==-2) { nodes[mask]={-1,0,0,i}; layers[0].push_back(mask); }
  }
  for(int cost=1;cost<=limit && nodes[target].op==-2;cost++){
    auto add=[&](Mask v,int op,Mask a,Mask b){
      if(nodes[v].op!=-2) return;
      nodes[v]={op,a,b,-1}; layers[cost].push_back(v);
    };
    if(allowNot) for(Mask a:layers[cost-1]) add(full^a,2,a,a);
    for(int i=0;i<=cost-1-i && nodes[target].op==-2;i++){
      int j=cost-1-i;
      for(Mask a:layers[i]){
        for(Mask b:layers[j]){
          if(i==j && a>=b) continue;
          add(a&b,0,a,b); add(a|b,1,a,b);
        }
        if(nodes[target].op!=-2) break;
      }
    }
  }
  if(nodes[target].op==-2) return 1;
  int next=rows+cols;
  auto emit=[&](auto&& self,Mask a)->int {
    auto &e=nodes[a];
    if(e.wire>=0) return e.wire;
    int i=self(self,e.left),j=self(self,e.right);
    e.wire=next++;
    std::cout << e.wire << " " << (e.op==0?"and":e.op==1?"or":"not") << " " << i << " " << j << "\n";
    return e.wire;
  };
  int out=emit(emit,target);
  std::cout << "out " << out << "\n";
}
