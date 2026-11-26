"""Direct gate-choice SAT encoding; finite tables, two-input AND/OR only."""
import argparse
import json
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def solve(table, control=None):
    count = len(table['input_masks'])
    budget = table['budget']
    cases = table['cases']
    ids = IDPool()
    cnf = CNF()
    values = [[ids.id(('v', w, c)) for c in range(cases)]
              for w in range(count + budget)]
    constants = {}
    for w, mask in enumerate(table['input_masks']):
        for c in range(cases):
            constants[values[w][c]] = bool(mask >> c & 1)

    def clause(literals):
        result = []
        for literal in literals:
            variable = abs(literal)
            if variable in constants:
                if constants[variable] == (literal > 0):
                    return
            else:
                result.append(literal)
        cnf.append(result)

    choices = []
    for gate in range(budget):
        wire = count + gate
        options = []
        for b in range(wire):
            for a in range(b):
                for op in ('and', 'or'):
                    # A constant or a copy is unnecessary in the circuits searched here.
                    if b < count:
                        ma, mb = table['input_masks'][a], table['input_masks'][b]
                        mask = ma & mb if op == 'and' else ma | mb
                        if mask in (0, (1 << cases) - 1, ma, mb):
                            continue
                    selected = ids.id(('s', gate, a, b, op))
                    options.append((selected, a, b, op))
                    for c in range(cases):
                        va, vb, z = values[a][c], values[b][c], values[wire][c]
                        if op == 'and':
                            clause([-selected, -z, va])
                            clause([-selected, -z, vb])
                            clause([-selected, z, -va, -vb])
                        else:
                            clause([-selected, z, -va])
                            clause([-selected, z, -vb])
                            clause([-selected, -z, va, vb])
        choices.append(options)
        cnf.extend(CardEnc.equals([x[0] for x in options], 1, vpool=ids,
                                  encoding=EncType.seqcounter).clauses)
        for c in range(cases):
            if gate == budget - 1:
                cnf.append([values[wire][c] if table['target'] >> c & 1
                            else -values[wire][c]])
        if control is not None:
            a, b, op = control[gate]
            a, b = sorted((a, b))
            cnf.append([next(x[0] for x in options if x[1:] == (a, b, op))])
    for gate in range(budget - 1):
        wire = count + gate
        cnf.append([s for options in choices[gate + 1:]
                    for s, a, b, _ in options if wire in (a, b)])
    if table.get('ordered'):
        for gate in range(1, budget):
            for old_s, old_a, old_b, _ in choices[gate-1]:
                for s, a, b, _ in choices[gate]:
                    if (b, a) < (old_b, old_a):
                        cnf.append([-old_s, -s])
    if table.get('use_all_inputs'):
        for wire in range(count):
            cnf.append([s for options in choices for s, a, b, _ in options
                        if wire in (a, b)])
    print('CNF', cnf.nv, len(cnf.clauses), flush=True)
    with Solver(name='cadical195', bootstrap_with=cnf) as solver:
        if not solver.solve():
            print('UNSAT for this search model', flush=True)
            return None
        model = set(solver.get_model())
    masks = list(table['input_masks'])
    result = []
    for options in choices:
        _, a, b, op = next(x for x in options if x[0] in model)
        result.append((len(masks), op, a, b))
        masks.append(masks[a] & masks[b] if op == 'and' else masks[a] | masks[b])
    assert masks[-1] == table['target']
    print('SAT; independently evaluated on every table row', flush=True)
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('table')
    parser.add_argument('output')
    parser.add_argument('--control')
    args = parser.parse_args()
    control = None
    if args.control:
        control = []
        for line in Path(args.control).read_text().splitlines():
            parts = line.split()
            if parts[0] != 'out':
                control.append((int(parts[2]), int(parts[3]), parts[1]))
    result = solve(json.loads(Path(args.table).read_text()), control)
    if result is not None:
        Path(args.output).write_text('\n'.join(' '.join(map(str, g)) for g in result)
                                   + '\nout ' + str(result[-1][0]) + '\n')
