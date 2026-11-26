"""Search a complete finite truth table for a three-output circuit window."""
import argparse
import json
import random
import time
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('table')
parser.add_argument('checkpoint')
parser.add_argument('--seconds',type=int,default=300)
parser.add_argument('--seed',type=int,default=20261126)
args = parser.parse_args()
data = json.loads(Path(args.table).read_text())
inputs = data['input_masks']
targets = data['target']
count = len(inputs)
budget = data['budget']
full = (1 << data['cases']) - 1
base_ancestors = data['base_ancestors']
random_source = random.Random(args.seed)
popcount = int.bit_count if hasattr(int,'bit_count') else lambda n: bin(n).count('1')
reference = [(a,b,operation=='or') for a,b,operation in data['reference_gates']]
reference_outputs = data['reference_outputs']


def evaluate(gates,negation,outputs,optimize=None,structured=True):
    values = list(inputs)
    ancestors = list(base_ancestors)
    for i,(left,right,is_or) in enumerate(gates):
        value = full ^ values[left] if i==negation else (
            values[left] | values[right] if is_or else values[left] & values[right])
        values.append(value)
        cone = ancestors[left] | (1 << (30+i))
        if i!=negation:
            cone |= ancestors[right]
        ancestors.append(cone)
    if optimize is not None:
        outputs[optimize] = min(range(len(values)),key=lambda wire: popcount(values[wire]^targets[optimize]))
    errors = sum(popcount(values[wire]^target) for wire,target in zip(outputs,targets))
    if not structured:
        return errors,errors
    used = (1<<30)-1
    appearances = 30
    for wire in outputs:
        used |= ancestors[wire]
        appearances += popcount(ancestors[wire])
    sharing = appearances-popcount(used)
    observed = False
    if used & (1 << (30+negation)):
        toggled = list(values)
        toggled[count+negation] = full ^ values[count+negation]
        for i in range(negation+1,len(gates)):
            left,right,is_or = gates[i]
            toggled[count+i] = toggled[left] | toggled[right] if is_or else toggled[left] & toggled[right]
        observed = any(values[wire]!=toggled[wire] for wire in outputs)
    penalty = (0 if observed else 768) + max(0,2-sharing)*384
    return errors+penalty,errors


def seed():
    dropped = random_source.randrange(len(reference))
    branch = random_source.randrange(2)
    wire_map = list(range(count))
    gates = []
    for i,(a,b,operation) in enumerate(reference):
        a,b = wire_map[a],wire_map[b]
        if i==dropped:
            wire_map.append((a,b)[branch])
        else:
            wire_map.append(count+len(gates))
            gates.append((a,b,operation))
    return gates,random_source.randrange(budget),[wire_map[o] for o in reference_outputs]


def save(gates,negation,outputs):
    result = {'gates':[[count+i,'not' if i==negation else 'or' if op else 'and',a,b]
                       for i,(a,b,op) in enumerate(gates)],'outputs':outputs}
    path = Path(args.checkpoint)
    temporary = path.with_suffix(path.suffix+'.tmp')
    temporary.write_text(json.dumps(result))
    temporary.replace(path)


control = evaluate(reference,-1,list(reference_outputs),structured=False)
assert control==(0,0)
print('CONTROL reference verified on all',data['cases'],'window inputs',flush=True)
started = time.monotonic()
iterations = 0
restart = 0
best = float('inf')
while time.monotonic()-started<args.seconds:
    gates,negation,outputs = seed()
    objective,errors = evaluate(gates,negation,outputs)
    plateau = 0
    for step in range(6000):
        if step%128==0 and time.monotonic()-started>=args.seconds:
            break
        if objective<best:
            best=objective
            save(gates,negation,outputs)
            print('iterations',iterations,'best_objective',objective,'exact_window_errors',errors,flush=True)
        if errors==0:
            save(gates,negation,outputs)
            print('WINDOW WITNESS matches all',data['cases'],'inputs',flush=True)
            raise SystemExit(0)
        candidate = list(gates)
        candidate_outputs = list(outputs)
        candidate_negation = negation
        changes = 1+(random_source.randrange(4) if random_source.randrange(10)==0 else 0)
        for _ in range(changes):
            index = random_source.randrange(budget)
            a,b,operation = candidate[index]
            choice = random_source.randrange(20)
            if choice==0:
                candidate_negation=index
            elif choice<4:
                operation=not operation
            elif choice%2:
                a=random_source.randrange(count+index)
            else:
                b=random_source.randrange(count+index)
            candidate[index]=(a,b,operation)
        ands=sum(i!=candidate_negation and not op for i,(_,_,op) in enumerate(candidate))
        iterations+=1
        if not data['min_and']<=ands<=data['max_and']:
            continue
        optimize = random_source.randrange(3) if step%12==0 else None
        candidate_score,candidate_errors=evaluate(candidate,candidate_negation,candidate_outputs,optimize)
        if candidate_score<=objective or (plateau>1200 and random_source.randrange(20000)<2):
            plateau=0 if candidate_score<objective else plateau+1
            gates=candidate;negation=candidate_negation;outputs=candidate_outputs
            objective=candidate_score;errors=candidate_errors
        else:
            plateau+=1
    restart+=1
    if restart%10==0:
        print('restarts',restart,'iterations',iterations,flush=True)
print('TIME LIMIT; no witness; full shard remains unexhausted',flush=True)
raise SystemExit(1)
