#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <queue>
#include <random>
#include <string>
#include <vector>

struct Gate { int left, right; bool is_or; };
struct Task {
  std::string id;
  uint32_t target;
  int budget;
  std::vector<Gate> baseline;
  int output;
};
struct Goal { size_t task; std::array<int,9> inverse; };

int main(int argc, char** argv) {
  if (argc!=2) return 2;
  int budget=std::stoi(argv[1]);
  if (budget<1 || budget>16) return 2;
  int task_count;
  std::cin>>task_count;
  std::vector<Task> tasks;
  for (int i=0;i<task_count;i++) {
    Task task;int gates;
    std::cin>>task.id>>task.target>>task.budget>>gates;
    for(int j=0;j<gates;j++) {
      int wire,left,right;std::string op;
      std::cin>>wire>>op>>left>>right;
      if(wire!=9+j || left>=wire || right>=wire || (op!="or" && op!="and"))return 2;
      task.baseline.push_back({left,right,op=="or"});
    }
    std::string word;std::cin>>word>>task.output;
    if(word!="out")return 2;
    tasks.push_back(task);
  }
  std::array<uint32_t,9> inputs{};
  for(int i=0;i<9;i++)for(int u=0;u<4;u++)for(int v=0;v<5;v++)
    if(i==u || i==4+v)inputs[i]|=1u<<(5*u+v);

  constexpr uint32_t space=1u<<20;
  std::vector<int> goal_index(space,-1);
  std::vector<Goal> goals;
  std::vector<uint8_t> distance(space,255);
  std::vector<uint32_t> frontier;
  for(size_t task=0;task<tasks.size();task++) {
    if(tasks[task].budget<budget)continue;
    std::array<int,4> rows{0,1,2,3};
    do {
      std::array<int,5> columns{0,1,2,3,4};
      do {
        uint32_t mask=0;
        Goal goal;goal.task=task;
        for(int u=0;u<4;u++)goal.inverse[rows[u]]=u;
        for(int v=0;v<5;v++)goal.inverse[4+columns[v]]=4+v;
        for(int u=0;u<4;u++)for(int v=0;v<5;v++)
          if(tasks[task].target>>(5*u+v)&1)mask|=1u<<(5*rows[u]+columns[v]);
        if(goal_index[mask]<0) {
          goal_index[mask]=goals.size();goals.push_back(goal);
          distance[mask]=0;frontier.push_back(mask);
        }
      } while(std::next_permutation(columns.begin(),columns.end()));
    } while(std::next_permutation(rows.begin(),rows.end()));
  }
  if(frontier.empty())return 2;
  std::cerr<<"budget "<<budget<<" distinct permuted goals "<<frontier.size()<<"\n";
  for(size_t index=0;index<frontier.size();index++) {
    uint32_t mask=frontier[index];uint8_t next=distance[mask]+1;
    for(int bit=0;bit<20;bit++) {
      uint32_t neighbor=mask^(1u<<bit);
      if(distance[neighbor]==255){distance[neighbor]=next;frontier.push_back(neighbor);}
    }
  }
  std::mt19937 random(20261126+budget);
  auto evaluate=[&](const std::array<Gate,16>& gates,int& output,uint32_t& mask) {
    std::array<uint32_t,25> values{};
    std::copy(inputs.begin(),inputs.end(),values.begin());
    int score=255;
    for(int i=0;i<budget;i++) {
      const auto gate=gates[i];
      auto value=gate.is_or ? values[gate.left]|values[gate.right] : values[gate.left]&values[gate.right];
      values[9+i]=value;
      if(distance[value]<score){score=distance[value];output=9+i;mask=value;}
    }
    return score;
  };
  auto publish=[&](const std::array<Gate,16>& gates,int output,uint32_t mask) {
    assert(goal_index[mask]>=0);
    const auto goal=goals[goal_index[mask]];
    const auto task=tasks[goal.task];
    std::array<uint32_t,25> values{};
    std::copy(inputs.begin(),inputs.end(),values.begin());
    for(int i=0;i<budget;i++) {
      auto gate=gates[i];
      if(gate.left<9)gate.left=goal.inverse[gate.left];
      if(gate.right<9)gate.right=goal.inverse[gate.right];
      values[9+i]=gate.is_or ? values[gate.left]|values[gate.right] : values[gate.left]&values[gate.right];
    }
    assert(values[output]==task.target && budget<=task.budget);
    std::cerr<<"FOUND "<<task.id<<" target "<<task.target<<" budget "<<budget<<"\n";
    for(int i=0;i<budget;i++) {
      auto gate=gates[i];
      if(gate.left<9)gate.left=goal.inverse[gate.left];
      if(gate.right<9)gate.right=goal.inverse[gate.right];
      std::cout<<9+i<<" "<<(gate.is_or ? "or":"and")<<" "<<gate.left<<" "<<gate.right<<"\n";
    }
    std::cout<<"out "<<output<<"\n";
  };
  std::vector<size_t> seeds;
  for(size_t i=0;i<tasks.size();i++)if(tasks[i].budget>=budget && tasks[i].baseline.size()==budget+1)seeds.push_back(i);
  for(const auto& task:tasks)if(task.budget>=budget && task.baseline.size()==budget) {
    std::array<Gate,16> gates{};
    std::copy(task.baseline.begin(),task.baseline.end(),gates.begin());
    int output=0;uint32_t mask=0;
    if(evaluate(gates,output,mask)==0){publish(gates,output,mask);return 0;}
  }
  int best=255;
  for(int restart=0;restart<2000;restart++) {
    std::array<Gate,16> gates{};
    if(!seeds.empty() && restart%3!=2) {
      const auto seed=tasks[seeds[random()%seeds.size()]];
      int drop=random()%seed.baseline.size(),branch=random()%2;
      std::vector<int> wire_map(9+seed.baseline.size());
      std::iota(wire_map.begin(),wire_map.begin()+9,0);int next=0;
      for(size_t i=0;i<seed.baseline.size();i++) {
        auto gate=seed.baseline[i];gate.left=wire_map[gate.left];gate.right=wire_map[gate.right];
        if(i==drop){wire_map[9+i]=branch ? gate.left:gate.right;continue;}
        wire_map[9+i]=9+next;gates[next++]=gate;
      }
    } else for(int i=0;i<budget;i++)gates[i]={int(random()%(9+i)),int(random()%(9+i)),bool(random()%2)};
    int output=0;uint32_t mask=0;
    int score=evaluate(gates,output,mask),plateau=0;
    for(int step=0;step<40000;step++) {
      if(score<best){best=score;std::cerr<<"restart "<<restart<<" distance "<<best<<"\n";}
      if(score==0){publish(gates,output,mask);return 0;}
      auto candidate=gates;
      int changes=1+(random()%8==0 ? random()%4:0);
      for(int i=0;i<changes;i++) {
        int gate=random()%budget;
        if(random()%3==0)candidate[gate].is_or=!candidate[gate].is_or;
        else if(random()%2)candidate[gate].left=random()%(9+gate);
        else candidate[gate].right=random()%(9+gate);
      }
      int candidate_output=0;uint32_t candidate_mask=0;
      int candidate_score=evaluate(candidate,candidate_output,candidate_mask);
      if(candidate_score<=score || (plateau>2000 && random()%10000<3)) {
        plateau=candidate_score<score ? 0:plateau+1;
        gates=candidate;score=candidate_score;output=candidate_output;mask=candidate_mask;
      } else plateau++;
    }
    if(restart%100==0)std::cerr<<"completed restart "<<restart<<"\n";
  }
  return 1;
}
