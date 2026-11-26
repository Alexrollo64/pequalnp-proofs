"""Finite promise-table synthesis using one selector for each possible gate."""
import argparse
import json
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.solvers import Solver


def synthesize(table, output_path, known_path=None):
    inputs = table['input_masks']
    count = len(inputs)
    cases = table['cases']
    budget = table['budget']
    target = table['target']
    ids = IDPool()
    formula = CNF()
    values = {}
    choices = []
    high_parents = []
    low_parents = []
    for wire, mask in enumerate(inputs):
        for case in range(cases):
            value = ids.id(('value', wire, case))
            values[wire, case] = value
            formula.append([value if mask >> case & 1 else -value])
    for gate in range(budget):
        wire = count + gate
        high = [ids.id(('high', gate, i)) for i in range(wire)]
        low = [ids.id(('low', gate, i)) for i in range(wire)]
        high_parents.append(high)
        low_parents.append(low)
        options = []
        for left in range(wire):
            for right in range(left + 1, wire):
                for operation in ('and', 'or'):
                    selector = ids.id(('gate', gate, left, right, operation))
                    options.append((selector, left, right, operation))
                    formula.extend([[-selector, low[left]], [-selector, high[right]]])
        choices.append(options)
        formula.extend(CardEnc.equals([s for s, _, _, _ in options], 1,
                                      vpool=ids, encoding=EncType.seqcounter).clauses)
        for selectors in (high, low):
            formula.extend(CardEnc.atmost(selectors, 1, vpool=ids,
                                         encoding=EncType.seqcounter).clauses)
        for case in range(cases):
            value = ids.id(('value', wire, case))
            values[wire, case] = value
            for selector, left, right, operation in options:
                a, b = values[left, case], values[right, case]
                if operation == 'and':
                    clauses = [[-value, a], [-value, b], [value, -a, -b]]
                else:
                    clauses = [[value, -a], [value, -b], [-value, a, b]]
                formula.extend([[-selector] + clause for clause in clauses])
    for case in range(cases):
        value = values[count + budget - 1, case]
        formula.append([value if target >> case & 1 else -value])
    # Eliminate permutations of independent gates by sorting their parent pairs.
    for gate in (range(1, budget) if known_path is None else ()):
        previous_high, previous_low = high_parents[gate - 1], low_parents[gate - 1]
        high, low = high_parents[gate], low_parents[gate]
        for old in range(len(previous_high)):
            for new in range(old):
                formula.append([-previous_high[old], -high[new]])
            for old_left in range(old):
                for new_left in range(old_left):
                    formula.append([-previous_high[old], -high[old],
                                    -previous_low[old_left], -low[new_left]])
    for gate in range(budget - 1):
        wire = count + gate
        formula.append([s for options in choices[gate + 1:]
                        for s, a, b, _ in options if wire in (a, b)])
    if known_path:
        gates = []
        for line in Path(known_path).read_text().splitlines():
            fields = line.split()
            if fields[0] == 'out':
                break
            a, b = sorted(map(int, fields[2:]))
            gates.append((a, b, fields[1]))
        assert len(gates) == budget
        for gate, (a, b, operation) in enumerate(gates):
            selector = next(s for s, left, right, op in choices[gate]
                            if (left, right, op) == (a, b, operation))
            formula.append([selector])
    print('CNF', formula.nv, len(formula.clauses), flush=True)
    with Solver(name='glucose42', bootstrap_with=formula) as solver:
        if not solver.solve():
            print('UNSAT for the encoded constraints', flush=True)
            return
        model = set(solver.get_model())
    masks = list(inputs)
    result = []
    for gate, options in enumerate(choices):
        _, a, b, operation = next(option for option in options if option[0] in model)
        masks.append(masks[a] & masks[b] if operation == 'and' else masks[a] | masks[b])
        result.append(f'{count + gate} {operation} {a} {b}')
    assert masks[-1] == target
    result.append(f'out {count + budget - 1}')
    Path(output_path).write_text('\n'.join(result) + '\n')
    print('SAT; witness independently evaluated on all promised inputs', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('table')
    parser.add_argument('output')
    parser.add_argument('--known')
    arguments = parser.parse_args()
    synthesize(json.loads(Path(arguments.table).read_text()), arguments.output, arguments.known)
