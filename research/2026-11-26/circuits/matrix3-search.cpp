#include <algorithm>
#include <array>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <random>
#include <string>
#include <vector>

constexpr int input_count=18;
constexpr int gate_count=44;
constexpr int sample_count=512;
constexpr int word_count=sample_count/64;
struct Gate { int left,right; bool is_or; };
struct Candidate {
  std::array<Gate,45> gates{};
  std::array<int,9> outputs{};
  int not_gate=-1;
  int size=gate_count;
};
using Bits=std::array<uint64_t,word_count>;
using Values=std::array<Bits,input_count+45>;

bool expected(uint32_t input,int output) {
  int row=output/3,column=output%3;
  for(int k=0;k<3;k++)
    if((input>>(3*row+k)&1) && (input>>(9+3*k+column)&1))return true;
  return false;
}

int evaluate_full(const Candidate& candidate) {
  for(uint32_t input=0;input<(1u<<18);input++) {
    std::array<bool,input_count+45> values{};
    for(int i=0;i<input_count;i++)values[i]=input>>i&1;
    for(int i=0;i<candidate.size;i++) {
      const auto gate=candidate.gates[i];
      assert(gate.left>=0 && gate.left<input_count+i && gate.right>=0 && gate.right<input_count+i);
      values[input_count+i]=(i==candidate.not_gate) ? !values[gate.left] :
          (gate.is_or ? values[gate.left]||values[gate.right] : values[gate.left]&&values[gate.right]);
    }
    for(int output=0;output<9;output++) {
      assert(candidate.outputs[output]>=0 && candidate.outputs[output]<input_count+candidate.size);
      if(values[candidate.outputs[output]]!=expected(input,output))return input;
    }
  }
  return -1;
}

Candidate schoolbook(std::mt19937& random) {
  Candidate result;result.size=45;
  std::array<int,9> order{};std::iota(order.begin(),order.end(),0);
  std::shuffle(order.begin(),order.end(),random);
  int next=0;
  for(int output:order) {
    std::array<int,3> terms{0,1,2};std::shuffle(terms.begin(),terms.end(),random);
    int start=next;
    for(int k:terms)result.gates[next++]={3*(output/3)+k,9+3*k+output%3,false};
    result.gates[next++]={input_count+start,input_count+start+1,true};
    result.gates[next++]={input_count+start+3,input_count+start+2,true};
    result.outputs[output]=input_count+next-1;
  }
  return result;
}

Candidate seed(std::mt19937& random) {
  auto original=schoolbook(random);
  Candidate result;int dropped=random()%45,branch=random()%2,next=0;
  std::array<int,input_count+45> map{};std::iota(map.begin(),map.begin()+input_count,0);
  for(int i=0;i<45;i++) {
    auto gate=original.gates[i];gate.left=map[gate.left];gate.right=map[gate.right];
    if(i==dropped){map[input_count+i]=branch ? gate.left:gate.right;continue;}
    map[input_count+i]=input_count+next;result.gates[next++]=gate;
  }
  for(int output=0;output<9;output++)result.outputs[output]=map[original.outputs[output]];
  result.not_gate=random()%gate_count;
  return result;
}

int and_count(const Candidate& candidate) {
  int count=0;
  for(int i=0;i<candidate.size;i++)if(i!=candidate.not_gate && !candidate.gates[i].is_or)count++;
  return count;
}

void emit(const Candidate& candidate) {
  std::cout<<"{\"input_count\":18,\"gates\":[";
  for(int i=0;i<candidate.size;i++) {
    auto gate=candidate.gates[i];if(i)std::cout<<",";
    std::cout<<"{\"op\":\""<<(i==candidate.not_gate ? "not" : gate.is_or ? "or":"and")
             <<"\",\"inputs\":["<<gate.left;
    if(i!=candidate.not_gate)std::cout<<","<<gate.right;
    std::cout<<"]}";
  }
  std::cout<<"],\"outputs\":[";
  for(int i=0;i<9;i++){if(i)std::cout<<",";std::cout<<candidate.outputs[i];}
  std::cout<<"]}\n";
}

int main(int argc,char** argv) {
  std::mt19937 random(20261126);
  if(argc==2 && std::string(argv[1])=="--verify-baseline") {
    auto baseline=schoolbook(random);
    assert(baseline.size==45 && baseline.not_gate==-1 && and_count(baseline)==27);
    assert(evaluate_full(baseline)==-1);
    std::cout<<"Baseline verified on all 262144 inputs: 45 gates, 27 AND, 18 OR, 0 NOT\n";
    return 0;
  }
  int seconds=argc>1 ? std::stoi(argv[1]):900;
  if(seconds<1)return 2;
  std::vector<uint32_t> samples{0,(1u<<18)-1};
  for(int i=0;i<18;i++){samples.push_back(1u<<i);samples.push_back(((1u<<18)-1)^(1u<<i));}
  for(int a=0;a<9;a++)for(int b=9;b<18;b++)samples.push_back((1u<<a)|(1u<<b));
  int permanent_samples=samples.size();
  while(samples.size()<sample_count) {
    uint32_t mask=0;
    int chance=std::array<int,3>{15,50,85}[random()%3];
    for(int i=0;i<18;i++)if(int(random()%100)<chance)mask|=1u<<i;
    samples.push_back(mask);
  }
  Values input_values{};std::array<Bits,9> targets{};
  auto rebuild_samples=[&]() {
    input_values={};targets={};
    for(int sample=0;sample<sample_count;sample++) {
      int word=sample/64;uint64_t bit=1ull<<(sample%64);
      for(int i=0;i<18;i++)if(samples[sample]>>i&1)input_values[i][word]|=bit;
      for(int output=0;output<9;output++)if(expected(samples[sample],output))targets[output][word]|=bit;
    }
  };
  rebuild_samples();
  auto evaluate=[&](Candidate& candidate,int optimize_output) {
    Values values=input_values;
    for(int gate_index=0;gate_index<gate_count;gate_index++) {
      auto gate=candidate.gates[gate_index];
      for(int word=0;word<word_count;word++)
        values[input_count+gate_index][word]=(gate_index==candidate.not_gate) ? ~values[gate.left][word] :
            (gate.is_or ? values[gate.left][word]|values[gate.right][word] : values[gate.left][word]&values[gate.right][word]);
    }
    if(optimize_output>=0) {
      int best=sample_count+1,best_wire=0;
      for(int wire=0;wire<input_count+gate_count;wire++) {
        int error=0;
        for(int word=0;word<word_count;word++)error+=__builtin_popcountll(values[wire][word]^targets[optimize_output][word]);
        if(error<best){best=error;best_wire=wire;}
      }
      candidate.outputs[optimize_output]=best_wire;
    }
    int score=0;
    for(int output=0;output<9;output++)for(int word=0;word<word_count;word++)
      score+=__builtin_popcountll(values[candidate.outputs[output]][word]^targets[output][word]);
    return score;
  };
  auto start=std::chrono::steady_clock::now();
  uint64_t iterations=0,restarts=0;int global_best=sample_count*9+1,epoch=0;
  auto expired=[&](){return std::chrono::steady_clock::now()-start>=std::chrono::seconds(seconds);};
  std::cerr<<"Unit L-meta-18919 shard 6: 44 gates, exactly 1 NOT, 23..33 AND\n";
  std::cerr<<"Samples "<<sample_count<<" permanent "<<permanent_samples<<" timebox_seconds "<<seconds<<"\n";
  while(!expired()) {
    auto candidate=seed(random);int score=evaluate(candidate,-1),plateau=0;
    for(int step=0;step<120000;step++) {
      if((step&2047)==0 && expired())break;
      if(score<global_best){global_best=score;std::cerr<<"epoch "<<epoch<<" iterations "<<iterations<<" best_sample_errors "<<score<<"\n";}
      if(score==0) {
        int counterexample=evaluate_full(candidate);
        if(counterexample==-1) {
          assert(candidate.size==44 && candidate.not_gate>=0 && and_count(candidate)>=23 && and_count(candidate)<=33);
          std::cerr<<"WITNESS VERIFIED on all 262144 inputs\n";emit(candidate);return 0;
        }
        int index=permanent_samples+random()%(sample_count-permanent_samples);
        samples[index]=counterexample;rebuild_samples();epoch++;global_best=sample_count*9+1;
        score=evaluate(candidate,-1);std::cerr<<"added_counterexample "<<counterexample<<"\n";
      }
      auto proposal=candidate;
      int changes=1+(random()%12==0 ? random()%5:0);
      for(int i=0;i<changes;i++) {
        int gate=random()%gate_count;
        int kind=random()%20;
        if(kind==0)proposal.not_gate=gate;
        else if(kind<4)proposal.gates[gate].is_or=!proposal.gates[gate].is_or;
        else if(kind%2)proposal.gates[gate].left=random()%(input_count+gate);
        else proposal.gates[gate].right=random()%(input_count+gate);
      }
      int ands=and_count(proposal);
      iterations++;
      if(ands<23 || ands>33)continue;
      int next_score=evaluate(proposal,(step%8==0) ? random()%9:-1);
      if(next_score<=score || (plateau>3000 && random()%20000<2)) {
        plateau=next_score<score ? 0:plateau+1;candidate=proposal;score=next_score;
      } else plateau++;
    }
    restarts++;
    if(restarts%10==0)std::cerr<<"restarts "<<restarts<<" iterations "<<iterations<<" best_sample_errors "<<global_best<<"\n";
  }
  std::cerr<<"TIMEBOX END iterations "<<iterations<<" restarts "<<restarts<<" best_sample_errors "<<global_best<<"; no witness; shard remains unexhausted\n";
  return 1;
}
