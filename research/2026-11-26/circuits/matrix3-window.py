"""Synthesize three matrix outputs while keeping six reference outputs fixed."""
from pathlib import Path
import importlib
import json
import random
import subprocess
import sys

verify = importlib.import_module('verify-matrix3').verify
cache = Path('work/pnp-tools/cache') if Path('work/pnp-tools/cache').is_dir() else Path('window-results')
cache.mkdir(parents=True,exist_ok=True)
small = '--small' in sys.argv
prefix_name = 'L-meta-18919-window-small' if small else 'L-meta-18919-window'
group = [0, 1, 3]
fixed = [output for output in range(9) if output not in group]
order = fixed + group
reference = {'input_count': 18, 'gates': [], 'outputs': [0]*9}
for output in order:
    row, column = divmod(output, 3)
    first = 18 + len(reference['gates'])
    for k in range(3):
        reference['gates'].append({'op': 'and', 'inputs': [3*row+k, 9+3*k+column]})
    reference['gates'].append({'op': 'or', 'inputs': [first, first+1]})
    reference['gates'].append({'op': 'or', 'inputs': [first+3, first+2]})
    reference['outputs'][output] = 18 + len(reference['gates']) - 1
prefix = reference['gates'][:30]
relevant = set()
for output in group:
    row, column = divmod(output, 3)
    for k in range(3):
        relevant.update([3*row+k, 9+3*k+column])
supports = [{i} for i in range(18)]
for gate in prefix:
    supports.append(set.union(*(supports[parent] for parent in gate['inputs'])))
parents = [wire for wire, support in enumerate(supports) if support <= relevant]
parent_index = {wire: index for index, wire in enumerate(parents)}
count = len(parents)
random_source = random.Random(20261126)
samples = [0, sum(1 << i for i in relevant)]
samples += [1 << i for i in sorted(relevant)]
if small:
    for output in group:
        row,column = divmod(output,3)
        samples += [(1<<(3*row+k)) | (1<<(9+3*k+column)) for k in range(3)]
else:
    samples += [(1 << a) | (1 << b) for a in relevant if a < 9 for b in relevant if b >= 9]
samples = list(dict.fromkeys(samples))
while len(samples) < (32 if small else 128):
    value = sum((random_source.randrange(2) << i) for i in sorted(relevant))
    if value not in samples:
        samples.append(value)


def problem(budget):
    masks = [0] * count
    targets = [0] * len(group)
    for case, assignment in enumerate(samples):
        values = [bool(assignment >> i & 1) for i in range(18)]
        for gate in prefix:
            a, b = gate['inputs']
            values.append((values[a] and values[b]) if gate['op']=='and' else (values[a] or values[b]))
        for index, wire in enumerate(parents):
            if values[wire]:
                masks[index] |= 1 << case
        for index, output in enumerate(group):
            row, column = divmod(output, 3)
            expected = any((assignment >> (3*row+k)&1) and
                           (assignment >> (9+3*k+column)&1) for k in range(3))
            if expected:
                targets[index] |= 1 << case
    return dict(input_masks=masks,cases=len(samples),target=targets,budget=budget,
                allow_not=True,not_count=1,min_and=5,max_and=15,ordered=True)


def assemble(solution):
    circuit = {'input_count':18,'gates':list(prefix),'outputs':list(reference['outputs'])}
    def actual(wire):
        return parents[wire] if wire<count else 48+wire-count
    for wire, operation, left, right in solution['gates']:
        assert wire == count + len(circuit['gates']) - 30
        inputs = [actual(left)]
        if operation != 'not':
            inputs.append(actual(right))
        circuit['gates'].append({'op':operation,'inputs':inputs})
    for output, wire in zip(group,solution['outputs']):
        circuit['outputs'][output] = actual(wire)
    return circuit


if '--full-table' in sys.argv:
    bits = sorted(relevant)
    samples[:] = [sum(((packed>>i)&1)<<bit for i,bit in enumerate(bits))
                  for packed in range(1<<len(bits))]
    table = problem(14)
    ancestors = [0]*18
    for i,gate in enumerate(prefix):
        ancestors.append((1<<i) | ancestors[gate['inputs'][0]] | ancestors[gate['inputs'][1]])
    table['base_ancestors'] = [ancestors[parent] for parent in parents]
    table['parent_wires'] = parents
    table['output_positions'] = group
    table['relevant_input_positions'] = bits
    table['reference_gates'] = []
    for gate in reference['gates'][30:]:
        mapped = [parent_index[wire] if wire<48 else count+wire-48 for wire in gate['inputs']]
        table['reference_gates'].append([mapped[0],mapped[1],gate['op']])
    table['reference_outputs'] = [count+4,count+9,count+14]
    path = cache/'L-meta-18919-full-window.json'
    path.write_text(json.dumps(table))
    text_path = path.with_suffix('.txt')
    lines = [f'{count} 14 {len(samples)} 5 15',
             ' '.join(map(str, table['base_ancestors']))]
    lines += [''.join(str(mask >> i & 1) for i in range(len(samples)))
              for mask in table['input_masks'] + table['target']]
    lines.append(str(len(table['reference_gates'])))
    lines += [f'{a} {b} {int(op == "or")}'
              for a,b,op in table['reference_gates']]
    lines.append(' '.join(map(str,table['reference_outputs'])))
    text_path.write_text('\n'.join(lines) + '\n')
    print(path)
    print(text_path)
    raise SystemExit(0)

if '--assemble' in sys.argv:
    index = sys.argv.index('--assemble')
    solution = json.loads(Path(sys.argv[index+1]).read_text())
    result = assemble(solution)
    report = verify(result)
    destination = Path(sys.argv[index+2])
    destination.write_text(json.dumps(result))
    destination.with_suffix('.check.json').write_text(json.dumps(report,indent=2))
    print(json.dumps(report,indent=2))
    raise SystemExit(0 if report['incorrect_output_values']==0 and report['within_shard_6'] else 2)

synthesize = importlib.import_module('synth-circuit').synthesize

control = problem(15)
control.update(not_count=0,ordered=False,repair_radius=0)
hint = []
for gate in reference['gates'][30:]:
    def remap(wire):
        return parent_index[wire] if wire<48 else count+wire-48
    hint.append([remap(gate['inputs'][0]),remap(gate['inputs'][1]),gate['op']])
control['hint'] = hint
print('CONTROL known 45-gate reference',flush=True)
solution = synthesize(**control)
assert solution is not None
report = verify(assemble(solution))
assert report['incorrect_output_values']==0 and report['gates']==45
print('CONTROL passed on all 262144 inputs',flush=True)
for iteration in range(8 if small else 3):
    specification = problem(14)
    if small:
        specification['output_wires'] = [count+13,None,None]
    source = cache / f'{prefix_name}-{iteration}.json'
    output = cache / f'{prefix_name}-{iteration}-solution.json'
    source.write_text(json.dumps(specification))
    output.unlink(missing_ok=True)
    print('WINDOW',group,'known signals',count,'sample count',len(samples),'iteration',iteration,flush=True)
    try:
        with open(cache/f'{prefix_name}-{iteration}.log','w') as log:
            result = subprocess.run([sys.executable,'-u',str(Path(__file__).with_name('synth-circuit.py')),str(source),str(output)],
                stdout=log,stderr=subprocess.STDOUT,timeout=60 if small else 90)
    except subprocess.TimeoutExpired:
        print('TIME LIMIT without verdict; full shard remains unexhausted',flush=True)
        break
    if result.returncode:
        raise SystemExit('Synthesis failed, inspect its log')
    if not output.exists():
        print('No witness for this encoded local window',flush=True)
        break
    solution = json.loads(output.read_text())
    circuit = assemble(solution)
    report = verify(circuit)
    assert all(report['outputs'][i]['errors']==0 for i in fixed)
    print('FULL CHECK',report['incorrect_output_values'],'incorrect output values',flush=True)
    (cache/f'{prefix_name}-{iteration}-candidate.json').write_text(json.dumps(circuit))
    (cache/f'{prefix_name}-{iteration}-check.json').write_text(json.dumps(report,indent=2))
    if report['incorrect_output_values']==0:
        assert report['within_shard_6']
        (cache/(prefix_name+'-verified.json')).write_text(json.dumps(circuit))
        print('VERIFIED WITNESS',flush=True)
        break
    counterexample = report['first_wrong_input']
    assert counterexample not in samples
    if small:
        added = 0
        bits = sorted(relevant)
        for packed in range(1<<len(bits)):
            assignment = sum(((packed>>i)&1)<<bit for i,bit in enumerate(bits))
            if assignment in samples:
                continue
            values = [bool(assignment>>i&1) for i in range(18)]
            for gate in circuit['gates']:
                parents = gate['inputs']
                if gate['op']=='not':
                    values.append(not values[parents[0]])
                elif gate['op']=='and':
                    values.append(values[parents[0]] and values[parents[1]])
                else:
                    values.append(values[parents[0]] or values[parents[1]])
            wrong = False
            for output in group:
                row,column = divmod(output,3)
                expected = any((assignment>>(3*row+k)&1) and
                    (assignment>>(9+3*k+column)&1) for k in range(3))
                if values[circuit['outputs'][output]]!=expected:
                    wrong = True
            if wrong:
                samples.append(assignment)
                added += 1
                if added==16:
                    break
        assert added>0
        print('Added',added,'counterexamples',flush=True)
    else:
        samples.append(counterexample)
