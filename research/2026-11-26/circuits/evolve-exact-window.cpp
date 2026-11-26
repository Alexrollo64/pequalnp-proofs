#include <algorithm>
#include <array>
#include <bitset>
#include <chrono>
#include <cstdio>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

using Bits=std::bitset<4096>;
struct Gate { int left,right;bool is_or; };
struct Candidate { std::array<Gate,16> gates{};std::array<int,3> outputs{};int size=14,negation=-1; };
struct Score { int objective,errors; };

int main(int argc,char** argv) {
  if(argc<4)return 2;
  int seconds=std::stoi(argv[1]);uint32_t random_seed=std::stoul(argv[2]);
  if(seconds<1)return 2;
  int count,budget,cases,min_and,max_and;
  std::cin>>count>>budget>>cases>>min_and>>max_and;
  if(count<1 || count>40 || budget<1 || budget>15 || cases!=4096 || count+budget>64)return 2;
  std::array<uint64_t,64> input_ancestors{};
  for(int i=0;i<count;i++)std::cin>>input_ancestors[i];
  std::array<Bits,64> inputs;
  std::array<Bits,3> targets;
  std::string bits;
  for(int i=0;i<count;i++){std::cin>>bits;if(bits.size()!=4096)return 2;inputs[i]=Bits(bits);}
  for(auto& target:targets){std::cin>>bits;if(bits.size()!=4096)return 2;target=Bits(bits);}
  Candidate reference;
  std::cin>>reference.size;
  if(reference.size!=budget+1 || reference.size>16)return 2;
  for(int i=0;i<reference.size;i++)std::cin>>reference.gates[i].left>>reference.gates[i].right>>reference.gates[i].is_or;
  for(auto& output:reference.outputs)std::cin>>output;
  if(!std::cin)return 2;
  auto evaluate=[&](Candidate& candidate,int optimize,bool structured) {
    std::array<Bits,64> values;
    std::copy(inputs.begin(),inputs.begin()+count,values.begin());
    auto ancestors=input_ancestors;
    for(int i=0;i<candidate.size;i++) {
      auto gate=candidate.gates[i];
      if(gate.left<0 || gate.left>=count+i || gate.right<0 || gate.right>=count+i)std::abort();
      values[count+i]=i==candidate.negation ? ~values[gate.left] :
          gate.is_or ? values[gate.left]|values[gate.right] : values[gate.left]&values[gate.right];
      ancestors[count+i]=ancestors[gate.left] | (1ull<<(30+i));
      if(i!=candidate.negation)ancestors[count+i]|=ancestors[gate.right];
    }
    if(optimize>=0) {
      int best=4097;
      for(int wire=0;wire<count+candidate.size;wire++) {
        int error=(values[wire]^targets[optimize]).count();
        if(error<best){best=error;candidate.outputs[optimize]=wire;}
      }
    }
    int errors=0,appearances=30;uint64_t used=(1ull<<30)-1;
    for(int output=0;output<3;output++) {
      int wire=candidate.outputs[output];
      errors+=(values[wire]^targets[output]).count();
      used|=ancestors[wire];appearances+=__builtin_popcountll(ancestors[wire]);
    }
    if(!structured)return Score{errors,errors};
    bool observed=false;
    if(used & (1ull<<(30+candidate.negation))) {
      auto toggled=values;
      toggled[count+candidate.negation]=~values[count+candidate.negation];
      for(int i=candidate.negation+1;i<candidate.size;i++) {
        auto gate=candidate.gates[i];
        toggled[count+i]=gate.is_or ? toggled[gate.left]|toggled[gate.right] : toggled[gate.left]&toggled[gate.right];
      }
      for(int wire:candidate.outputs)if(values[wire]!=toggled[wire])observed=true;
    }
    int shared=appearances-__builtin_popcountll(used);
    return Score{errors+(observed ? 0:768)+384*std::max(0,2-shared),errors};
  };
  if(evaluate(reference,-1,false).errors!=0)return 3;
  std::cerr<<"CONTROL reference correct on all 4096 window inputs\n";
  std::mt19937 random(random_seed);
  auto seed=[&]() {
    Candidate candidate;candidate.size=budget;
    int dropped=random()%reference.size,branch=random()%2,next=0;
    std::vector<int> map(count+reference.size);std::iota(map.begin(),map.begin()+count,0);
    for(int i=0;i<reference.size;i++) {
      auto gate=reference.gates[i];gate.left=map[gate.left];gate.right=map[gate.right];
      if(i==dropped){map[count+i]=branch ? gate.left:gate.right;continue;}
      map[count+i]=count+next;candidate.gates[next++]=gate;
    }
    for(int output=0;output<3;output++)candidate.outputs[output]=map[reference.outputs[output]];
    candidate.negation=random()%budget;return candidate;
  };
  auto emit=[&](const Candidate& candidate,std::ostream& out) {
    out<<"{\"gates\":[";
    for(int i=0;i<budget;i++) {
      auto gate=candidate.gates[i];if(i)out<<",";
      out<<"["<<count+i<<",\""<<(i==candidate.negation ? "not" : gate.is_or ? "or":"and")<<"\","<<gate.left<<","<<gate.right<<"]";
    }
    out<<"],\"outputs\":[";
    for(int i=0;i<3;i++){if(i)out<<",";out<<candidate.outputs[i];}
    out<<"]}\n";
  };
  auto save=[&](const Candidate& candidate) {
    std::string temporary=std::string(argv[3])+".tmp";
    {std::ofstream out(temporary);emit(candidate,out);}
    std::rename(temporary.c_str(),argv[3]);
  };
  auto start=std::chrono::steady_clock::now();
  auto expired=[&](){return std::chrono::steady_clock::now()-start>=std::chrono::seconds(seconds);};
  uint64_t iterations=0,restarts=0;int global_best=1000000;
  while(!expired()) {
    auto candidate=seed();auto score=evaluate(candidate,-1,true);int plateau=0;
    for(int step=0;step<100000;step++) {
      if((step&1023)==0 && expired())break;
      if(score.objective<global_best) {
        global_best=score.objective;save(candidate);
        std::cerr<<"iterations "<<iterations<<" best_objective "<<global_best<<" exact_window_errors "<<score.errors<<"\n";
      }
      if(score.errors==0){save(candidate);emit(candidate,std::cout);std::cerr<<"WINDOW WITNESS correct on all 4096 inputs\n";return 0;}
      auto proposal=candidate;
      int changes=1+(random()%10==0 ? random()%5:0);
      for(int i=0;i<changes;i++) {
        int gate=random()%budget,kind=random()%20;
        if(kind==0)proposal.negation=gate;
        else if(kind<4)proposal.gates[gate].is_or=!proposal.gates[gate].is_or;
        else if(kind%2)proposal.gates[gate].left=random()%(count+gate);
        else proposal.gates[gate].right=random()%(count+gate);
      }
      int ands=0;for(int i=0;i<budget;i++)if(i!=proposal.negation && !proposal.gates[i].is_or)ands++;
      iterations++;if(ands<min_and || ands>max_and)continue;
      auto next=evaluate(proposal,step%12==0 ? random()%3:-1,true);
      if(next.objective<=score.objective || (plateau>2000 && random()%20000<2)) {
        plateau=next.objective<score.objective ? 0:plateau+1;candidate=proposal;score=next;
      } else plateau++;
    }
    restarts++;if(restarts%10==0)std::cerr<<"restarts "<<restarts<<" iterations "<<iterations<<"\n";
  }
  std::cerr<<"TIME LIMIT without witness; full shard remains unexhausted\n";return 1;
}
