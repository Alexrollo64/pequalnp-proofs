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
#include <fstream>
#include <cstdio>
#include <queue>
#include <unordered_set>

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
  std::array<int,48> base_parents{};
  int base_parent_count=0;
  std::array<int,3> group_outputs{};
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

Candidate seed(std::mt19937& random,bool grouped=false) {
  auto original=schoolbook(random);
  Candidate result;int dropped=grouped ? 30+random()%15 : random()%45;
  int branch=random()%2,next=0;
  std::array<int,input_count+45> map{};std::iota(map.begin(),map.begin()+input_count,0);
  for(int i=0;i<45;i++) {
    auto gate=original.gates[i];gate.left=map[gate.left];gate.right=map[gate.right];
    if(i==dropped){map[input_count+i]=branch ? gate.left:gate.right;continue;}
    map[input_count+i]=input_count+next;result.gates[next++]=gate;
  }
  for(int output=0;output<9;output++)result.outputs[output]=map[original.outputs[output]];
  result.not_gate=grouped ? 30+random()%14 : random()%gate_count;
  if(grouped) {
    uint32_t relevant=0;int index=0;
    for(int output=0;output<9;output++)if(original.outputs[output]>=input_count+30) {
      result.group_outputs[index++]=output;
      for(int k=0;k<3;k++) {
        relevant|=1u<<(3*(output/3)+k);
        relevant|=1u<<(9+3*k+output%3);
      }
    }
    assert(index==3);
    std::array<uint32_t,input_count+30> supports{};
    for(int i=0;i<input_count;i++)supports[i]=1u<<i;
    for(int i=0;i<30;i++)supports[input_count+i]=supports[result.gates[i].left]|supports[result.gates[i].right];
    for(int i=0;i<input_count+30;i++)if((supports[i]&~relevant)==0)
      result.base_parents[result.base_parent_count++]=i;
  }
  return result;
}

int and_count(const Candidate& candidate) {
  int count=0;
  for(int i=0;i<candidate.size;i++)if(i!=candidate.not_gate && !candidate.gates[i].is_or)count++;
  return count;
}

struct SharingInfo { int active, repeated_appearances; bool not_gate_active; };

SharingInfo analyze_sharing(const Candidate& candidate) {
  std::array<uint64_t,input_count+45> ancestors{};
  for(int i=0;i<candidate.size;i++) {
    auto gate=candidate.gates[i];
    auto cone=ancestors[gate.left] | (1ull<<i);
    if(i!=candidate.not_gate)cone|=ancestors[gate.right];
    ancestors[input_count+i]=cone;
  }
  uint64_t used=0;int appearances=0;
  for(int output:candidate.outputs) {
    used|=ancestors[output];
    appearances+=__builtin_popcountll(ancestors[output]);
  }
  int active=__builtin_popcountll(used);
  bool not_gate_active=candidate.not_gate>=0 && ((used>>candidate.not_gate)&1);
  return {active,appearances-active,not_gate_active};
}

void emit(const Candidate& candidate, std::ostream& stream=std::cout) {
  stream<<"{\"input_count\":18,\"gates\":[";
  for(int i=0;i<candidate.size;i++) {
    auto gate=candidate.gates[i];if(i)stream<<",";
    stream<<"{\"op\":\""<<(i==candidate.not_gate ? "not" : gate.is_or ? "or":"and")
             <<"\",\"inputs\":["<<gate.left;
    if(i!=candidate.not_gate)stream<<","<<gate.right;
    stream<<"]}";
  }
  stream<<"],\"outputs\":[";
  for(int i=0;i<9;i++){if(i)stream<<",";stream<<candidate.outputs[i];}
  stream<<"]}\n";
}

int main(int argc,char** argv) {
  uint32_t random_seed=argc>2 ? std::stoul(argv[2]):20261126;
  std::mt19937 random(random_seed);
  if(argc==2 && std::string(argv[1])=="--emit-baseline") { emit(schoolbook(random)); return 0; }
  if(argc==2 && std::string(argv[1])=="--verify-baseline") {
    auto baseline=schoolbook(random);
    assert(baseline.size==45 && baseline.not_gate==-1 && and_count(baseline)==27);
    assert(evaluate_full(baseline)==-1);
    std::cout<<"Baseline verified on all 262144 inputs: 45 gates, 27 AND, 18 OR, 0 NOT\n";
    return 0;
  }
  bool repair=argc>4 && std::string(argv[4])=="repair";
  bool grouped=argc>4 && std::string(argv[4])=="grouped";
  bool structured=repair || grouped || (argc>4 && std::string(argv[4])=="structured");
  bool observable=repair || (argc>5 && std::string(argv[5])=="observable");
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
  auto evaluate=[&](Candidate& candidate,int optimize_output,int* raw_errors=nullptr) {
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
    if(raw_errors)*raw_errors=score;
    if(structured) {
      auto sharing=analyze_sharing(candidate);
      bool not_observed=sharing.not_gate_active;
      if(observable && not_observed) {
        Values toggled=values;
        for(int word=0;word<word_count;word++)
          toggled[input_count+candidate.not_gate][word]=~values[input_count+candidate.not_gate][word];
        for(int i=candidate.not_gate+1;i<gate_count;i++) {
          auto gate=candidate.gates[i];
          for(int word=0;word<word_count;word++)
            toggled[input_count+i][word]=gate.is_or ? toggled[gate.left][word]|toggled[gate.right][word] :
                toggled[gate.left][word]&toggled[gate.right][word];
        }
        not_observed=false;
        for(int output:candidate.outputs)for(int word=0;word<word_count;word++)
          if(toggled[output][word]!=values[output][word])not_observed=true;
      }
      score+=(not_observed ? 0:96)+48*std::max(0,2-sharing.repeated_appearances);
    }
    return score;
  };
  auto start=std::chrono::steady_clock::now();
  uint64_t iterations=0,restarts=0;int global_best=sample_count*9+1,epoch=0;
  auto expired=[&](){return std::chrono::steady_clock::now()-start>=std::chrono::seconds(seconds);};
  std::cerr<<"Unit L-meta-18919 shard 6: 44 gates, exactly 1 NOT, 23..33 AND\n";
  std::cerr<<"random_seed "<<random_seed<<" structured "<<structured<<" grouped "<<grouped<<" observable "<<observable<<"\n";
  std::cerr<<"Samples "<<sample_count<<" permanent "<<permanent_samples<<" timebox_seconds "<<seconds<<"\n";
  if(repair) {
    if(argc<6)return 2;
    Candidate initial;int bad_output;
    std::ifstream source(argv[5]);
    source>>initial.not_gate>>bad_output;
    for(int i=0;i<gate_count;i++)source>>initial.gates[i].left>>initial.gates[i].right>>initial.gates[i].is_or;
    for(auto& output:initial.outputs)source>>output;
    if(!source || initial.not_gate<0 || initial.not_gate>=gate_count || bad_output<0 || bad_output>=9)return 2;
    for(int i=0;i<gate_count;i++) {
      auto gate=initial.gates[i];
      if(gate.left<0 || gate.left>=input_count+i || gate.right<0 || gate.right>=input_count+i)return 2;
    }
    struct Scored {
      int score;uint64_t hash;Candidate candidate;
      bool operator<(const Scored& other)const{return score<other.score;}
    };
    auto fingerprint=[](const Candidate& candidate) {
      uint64_t result=1469598103934665603ull;
      for(int i=0;i<gate_count;i++) {
        auto gate=candidate.gates[i];
        for(auto part:{gate.left,gate.right,int(gate.is_or)})result=(result^uint64_t(part+1))*1099511628211ull;
      }
      for(int wire:candidate.outputs)result=(result^uint64_t(wire+1))*1099511628211ull;
      return result;
    };
    int raw=0;int score=evaluate(initial,-1,&raw);
    std::vector<Scored> beam{{score,fingerprint(initial),initial}};
    std::cerr<<"REPAIR initial_objective "<<score<<" sample_errors "<<raw<<" output "<<bad_output<<"\n";
    for(int level=0;level<3;level++) {
      std::priority_queue<Scored> best;
      std::unordered_set<uint64_t> selected;
      for(const auto& base:beam)for(int gate=0;gate<gate_count;gate++) {
        int parent_count=input_count+gate;
        for(int left=0;left<parent_count;left++)for(int right=left;right<parent_count;right++) {
          if(gate==initial.not_gate && right!=left)continue;
          for(bool is_or:{false,true}) {
            if(gate==initial.not_gate && is_or)continue;
            if((iterations&1023)==0 && expired()) {
              std::cerr<<"REPAIR TIMEBOX iterations "<<iterations<<" full shard remains unexhausted\n";return 1;
            }
            Candidate proposal=base.candidate;
            proposal.gates[gate]={left,right,is_or};iterations++;
            int ands=and_count(proposal);if(ands<23 || ands>33)continue;
            int errors=0;int objective=evaluate(proposal,bad_output,&errors);
            if(errors==0) {
              int counterexample=evaluate_full(proposal);
              if(counterexample==-1) {
                std::cerr<<"WITNESS VERIFIED on all 262144 inputs\n";emit(proposal);return 0;
              }
              std::cerr<<"REPAIR sample witness rejected by full input "<<counterexample<<"\n";
              if(argc>3){std::ofstream checkpoint(argv[3]);emit(proposal,checkpoint);}return 3;
            }
            if(best.size()>=16 && objective>best.top().score)continue;
            auto hash=fingerprint(proposal);if(selected.count(hash))continue;
            if(best.size()>=16){selected.erase(best.top().hash);best.pop();}
            best.push({objective,hash,proposal});selected.insert(hash);
          }
        }
      }
      beam.clear();while(!best.empty()){beam.push_back(best.top());best.pop();}
      std::reverse(beam.begin(),beam.end());
      if(beam.empty())return 1;
      int errors=0;evaluate(beam.front().candidate,-1,&errors);
      std::cerr<<"REPAIR level "<<level<<" iterations "<<iterations<<" best_objective "<<beam.front().score<<" sample_errors "<<errors<<"\n";
      if(argc>3){std::ofstream checkpoint(argv[3]);emit(beam.front().candidate,checkpoint);}
    }
    std::cerr<<"REPAIR END without witness; full shard remains unexhausted\n";return 1;
  }
  while(!expired()) {
    auto candidate=seed(random,grouped);int raw_errors=0;
    int score=evaluate(candidate,-1,&raw_errors),plateau=0;
    for(int step=0;step<120000;step++) {
      if((step&2047)==0 && expired())break;
      if(score<global_best){
        global_best=score;
        std::cerr<<"epoch "<<epoch<<" iterations "<<iterations<<" best_objective "<<score<<" sample_errors "<<raw_errors<<"\n";
        if(argc>3) {
          std::string temporary=std::string(argv[3])+".tmp";
          { std::ofstream checkpoint(temporary);emit(candidate,checkpoint); }
          std::rename(temporary.c_str(),argv[3]);
        }
      }
      if(raw_errors==0) {
        int counterexample=evaluate_full(candidate);
        if(counterexample==-1) {
          assert(candidate.size==44 && candidate.not_gate>=0 && and_count(candidate)>=23 && and_count(candidate)<=33);
          std::cerr<<"WITNESS VERIFIED on all 262144 inputs\n";emit(candidate);return 0;
        }
        int index=permanent_samples+random()%(sample_count-permanent_samples);
        samples[index]=counterexample;rebuild_samples();epoch++;global_best=sample_count*9+1;
        score=evaluate(candidate,-1,&raw_errors);std::cerr<<"added_counterexample "<<counterexample<<"\n";
      }
      auto proposal=candidate;
      int changes=1+(random()%12==0 ? random()%5:0);
      for(int i=0;i<changes;i++) {
        int gate=grouped ? 30+random()%14 : random()%gate_count;
        int kind=random()%20;
        if(kind==0)proposal.not_gate=gate;
        else if(kind<4)proposal.gates[gate].is_or=!proposal.gates[gate].is_or;
        else {
          int parent;
          if(grouped) {
            int choice=random()%(proposal.base_parent_count+gate-30);
            parent=choice<proposal.base_parent_count ? proposal.base_parents[choice] :
                input_count+30+choice-proposal.base_parent_count;
          } else parent=random()%(input_count+gate);
          if(kind%2)proposal.gates[gate].left=parent;
          else proposal.gates[gate].right=parent;
        }
      }
      int ands=and_count(proposal);
      iterations++;
      if(ands<23 || ands>33)continue;
      int next_raw_errors=0;
      int optimize_output=-1;
      if(step%8==0)optimize_output=grouped ? proposal.group_outputs[random()%3] : random()%9;
      int next_score=evaluate(proposal,optimize_output,&next_raw_errors);
      if(next_score<=score || (plateau>3000 && random()%20000<2)) {
        plateau=next_score<score ? 0:plateau+1;candidate=proposal;score=next_score;raw_errors=next_raw_errors;
      } else plateau++;
    }
    restarts++;
    if(restarts%10==0)std::cerr<<"restarts "<<restarts<<" iterations "<<iterations<<" best_objective "<<global_best<<"\n";
  }
  std::cerr<<"TIMEBOX END iterations "<<iterations<<" restarts "<<restarts<<" best_objective "<<global_best<<"; no witness; shard remains unexhausted\n";
  return 1;
}
