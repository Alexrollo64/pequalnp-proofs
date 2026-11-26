"""Produce a Lean replay proof for the desk's nine-output matrix-product statement."""
import argparse
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('circuit')
parser.add_argument('desk_record')
parser.add_argument('output')
parser.add_argument('--module')
parser.add_argument('--limit',type=int,default=44)
args = parser.parse_args()
data = json.loads(Path(args.desk_record).read_text())
gap = data.get('gap',data)
module = args.module or gap.get('module') or gap['assigned_module']
if args.limit != 44 and args.module is None:
    raise ValueError('A reference control uses its own theorem name')
statement = gap['statement']
assert 'C.size ≤ 44' in statement
if args.limit != 44:
    statement = statement.replace('C.size ≤ 44','C.size ≤ '+str(args.limit),1)
circuit = json.loads(Path(args.circuit).read_text())
assert circuit['input_count'] == 18 and len(circuit['outputs']) == 9
assert len(circuit['gates']) <= args.limit
imports = gap.get('imports') or gap['assigned_imports']
assert 'PEqualNP.Library.Helpers.ReplayColExpr' in imports
namespace = module + '_aux'
lines = ['import '+name for name in imports]
lines += ['', 'namespace '+namespace,
          'open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity',
          'open PEqualNP.Library.Helpers.ReplayCol PEqualNP.Library.Helpers.ReplayColExpr',
          '', 'def circuit : Circuit :=', '  ⟨[']
for index,gate in enumerate(circuit['gates']):
    assert gate['op'] in ('and','or','not')
    parents = gate['inputs']
    assert len(parents) == (1 if gate['op']=='not' else 2)
    assert all(0 <= p < 18+index for p in parents)
    comma = ',' if index+1 < len(circuit['gates']) else ''
    lines.append('    ⟨.'+gate['op']+', ['+', '.join(map(str,parents))+']⟩'+comma)
lines += ['  ], '+str(circuit['outputs'][-1])+'⟩','',
          'def outputs (v : Fin 9) : ℕ := !['+', '.join(map(str,circuit['outputs']))+'] v','',
          'theorem fanin : FanInTwo circuit := by',
          '  intro g hg',
          '  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg',
          '  rcases hg with '+' | '.join(['rfl']*len(circuit['gates']))+' <;> simp','']
for output in range(9):
    row,column = divmod(output,3)
    pairs = [(3*row+k,9+3*k+column) for k in range(3)]
    boolean = ' || '.join(f'x {a} && x {b}' for a,b in pairs)
    columns = ' ||| '.join(f'((inCol 18 {a}) &&& (inCol 18 {b}))' for a,b in pairs)
    lines += ['set_option maxRecDepth 8192 in',
              'set_option maxHeartbeats 2000000 in',
              f'theorem wire{output} : ∀ x : Fin 18 → Bool,',
              f'    (circuit.wires (List.ofFn x)).getD (outputs {output}) false = ({boolean}) := by',
              f'  apply wire_of_expr (C := circuit) (n := 18) (f := fun x => {boolean})',
              f'    (outputs {output}) ({columns})',
              '  · decide',
              '  · decide +kernel',
              '  · intro x',
              '    simp [Nat.testBit_or, Nat.testBit_and, inCol_bit]', '']
lines += ['end '+namespace, '', 'theorem '+module+' : ('+statement+') := by',
          '  refine ⟨'+namespace+'.circuit, '+namespace+'.outputs, '+namespace+'.fanin, by decide, ?_⟩',
          '  intro x', '  exact ⟨'+', '.join(namespace+'.wire'+str(i)+' x' for i in range(9))+'⟩','']
Path(args.output).write_text('\n'.join(lines))
