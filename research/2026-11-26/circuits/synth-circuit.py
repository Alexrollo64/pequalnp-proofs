"""Synthesize an AND/OR circuit against an explicitly finite promise table."""
import argparse
import json
from pathlib import Path
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def synthesize(input_masks, cases, target, budget, allow_not=False, ordered=False,
               hint=None, repair_radius=None, minimal=False, fanout=False,
               not_count=None, min_and=None, max_and=None, solver_name='cadical195',
               output_wires=None, certificate_prefix=None):
    ids = IDPool()
    formula = CNF()
    input_count = len(input_masks)
    multiple_outputs = isinstance(target, list)
    values = {}
    for wire, mask in enumerate(input_masks):
        for case in range(cases):
            variable = ids.id(('wire', wire, case))
            values[wire, case] = variable
            formula.append([variable if mask >> case & 1 else -variable])
    choices = []
    for gate in range(budget):
        wire = input_count + gate
        left = [ids.id(('left', gate, parent)) for parent in range(wire)]
        right = [ids.id(('right', gate, parent)) for parent in range(wire)]
        for selectors in (left, right):
            formula.extend(CardEnc.equals(selectors, 1, vpool=ids,
                                          encoding=EncType.seqcounter).clauses)
        # Commutativity permits sorting the two parent indices.
        for a in range(wire):
            for b in range(a):
                formula.append([-left[a], -right[b]])
        operation = [ids.id(('op', gate, op)) for op in range(3 if allow_not else 2)]
        formula.extend(CardEnc.equals(operation, 1, vpool=ids,
                                      encoding=EncType.seqcounter).clauses)
        choices.append((left, right, operation))
        for case in range(cases):
            a = ids.id(('a', gate, case))
            b = ids.id(('b', gate, case))
            z = ids.id(('wire', wire, case))
            values[wire, case] = z
            for parent in range(wire):
                x = values[parent, case]
                formula.extend([[-left[parent], -a, x], [-left[parent], a, -x],
                                [-right[parent], -b, x], [-right[parent], b, -x]])
            and_op, or_op = operation[:2]
            formula.extend([[-and_op, -z, a], [-and_op, -z, b],
                            [-and_op, z, -a, -b],
                            [-or_op, z, -a], [-or_op, z, -b],
                            [-or_op, -z, a, b]])
            if allow_not:
                not_op = operation[2]
                formula.extend([[-not_op, -z, -a], [-not_op, z, a]])
        if gate == budget - 1 and not multiple_outputs:
            for case in range(cases):
                z = values[wire, case]
                formula.append([z if target >> case & 1 else -z])
    output_selectors = []
    if multiple_outputs:
        for output, expected in enumerate(target):
            selectors = [ids.id(('output', output, wire))
                         for wire in range(input_count + budget)]
            output_selectors.append(selectors)
            formula.extend(CardEnc.equals(selectors, 1, vpool=ids,
                                          encoding=EncType.seqcounter).clauses)
            if output_wires is not None and output_wires[output] is not None:
                formula.append([selectors[output_wires[output]]])
            for wire, selector in enumerate(selectors):
                for case in range(cases):
                    value = values[wire, case]
                    formula.append([-selector, value if expected >> case & 1 else -value])
    if not_count is not None:
        negations = [ops[2] for _, _, ops in choices if len(ops) == 3]
        formula.extend(CardEnc.equals(negations, not_count, vpool=ids,
                                      encoding=EncType.seqcounter).clauses)
    conjunctions = [ops[0] for _, _, ops in choices]
    if min_and is not None:
        formula.extend(CardEnc.atleast(conjunctions, min_and, vpool=ids,
                                       encoding=EncType.seqcounter).clauses)
    if max_and is not None and max_and < budget:
        formula.extend(CardEnc.atmost(conjunctions, max_and, vpool=ids,
                                      encoding=EncType.seqcounter).clauses)
    if ordered:
        for gate in range(1, budget):
            old_left, old_right, _ = choices[gate - 1]
            left, right, _ = choices[gate]
            for old_parent in range(len(old_right)):
                for parent in range(old_parent):
                    formula.append([-old_right[old_parent], -right[parent]])
                for old_a in range(old_parent + 1):
                    for a in range(old_a):
                        formula.append([-old_right[old_parent], -right[old_parent],
                                        -old_left[old_a], -left[a]])
        for gate in range(budget - 1):
            wire = input_count + gate
            uses = [selector for left, right, _ in choices[gate + 1:]
                    for selector in (left[wire], right[wire])]
            uses.extend(selectors[wire] for selectors in output_selectors)
            formula.append(uses)
    phases = []
    changes = []
    if minimal:
        for primary in range(input_count):
            formula.append([selector for left, right, _ in choices
                            for selector in (left[primary], right[primary])])
        for gate in range(budget):
            wire = input_count + gate
            formula.append([values[wire, case] for case in range(cases)])
            formula.append([-values[wire, case] for case in range(cases)])
            for parent in range(wire):
                differences = []
                for case in range(cases):
                    diff = ids.id(('diff', wire, parent, case))
                    a, b = values[wire, case], values[parent, case]
                    formula.extend([[-diff, a, b], [-diff, -a, -b],
                                    [diff, a, -b], [diff, -a, b]])
                    differences.append(diff)
                formula.append(differences)
    if fanout:
        repeats = []
        for wire in range(input_count + budget - 1):
            selectors = [selector for gate, (left, right, _) in enumerate(choices)
                         if wire < input_count + gate
                         for selector in (left[wire], right[wire])]
            twice = ids.id(('twice', wire))
            thrice = ids.id(('thrice', wire))
            repeats.extend([twice, thrice])
            for maximum, flag in ((1, twice), (2, thrice)):
                bound = CardEnc.atmost(selectors, maximum, vpool=ids,
                                      encoding=EncType.seqcounter)
                formula.extend([clause + [flag] for clause in bound.clauses])
            formula.extend(CardEnc.atmost(selectors, 3, vpool=ids,
                                         encoding=EncType.seqcounter).clauses)
        formula.extend(CardEnc.atmost(repeats, budget - input_count + 1,
                                     vpool=ids, encoding=EncType.seqcounter).clauses)
    if hint:
        for gate, (a, b, op) in enumerate(hint):
            if a > b and op != 'not':
                a, b = b, a
            left, right, operations = choices[gate]
            phases.extend([left[a], right[b], operations[['and', 'or', 'not'].index(op)]])
            if repair_radius is not None:
                changed = ids.id(('changed', gate))
                changes.append(changed)
                for selected in phases[-3:]:
                    formula.append([changed, selected])
        if repair_radius is not None:
            formula.extend(CardEnc.atmost(changes, repair_radius, vpool=ids,
                                         encoding=EncType.seqcounter).clauses)
    print('CNF', formula.nv, len(formula.clauses), flush=True)
    if certificate_prefix is not None:
        formula.to_file(str(certificate_prefix) + '.cnf')
    with Solver(name=solver_name, bootstrap_with=formula,
                with_proof=certificate_prefix is not None) as solver:
        if phases:
            solver.set_phases(phases)
        if not solver.solve():
            if certificate_prefix is not None:
                proof = solver.get_proof()
                assert proof and proof[-1].strip() == '0'
                Path(str(certificate_prefix) + '.drat').write_text('\n'.join(proof) + '\n')
            print('UNSAT', flush=True)
            return None
        model = set(solver.get_model())
    masks = list(input_masks)
    gates = []
    for left, right, operation in choices:
        a = next(i for i, selected in enumerate(left) if selected in model)
        b = next(i for i, selected in enumerate(right) if selected in model)
        op = next(i for i, selected in enumerate(operation) if selected in model)
        gate = ['and', 'or', 'not'][op]
        value = (masks[a] & masks[b]) if op == 0 else ((masks[a] | masks[b]) if op == 1 else ((1 << cases) - 1) ^ masks[a])
        gates.append((len(masks), gate, a, b))
        masks.append(value)
    if multiple_outputs:
        outputs = [next(wire for wire, selected in enumerate(selectors) if selected in model)
                   for selectors in output_selectors]
        assert [masks[wire] for wire in outputs] == target
        print('SAT', json.dumps({'gates': gates, 'outputs': outputs}), flush=True)
        return {'gates': gates, 'outputs': outputs}
    assert masks[-1] == target
    print('SAT', json.dumps(gates), flush=True)
    return gates


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('table')
    parser.add_argument('output')
    args = parser.parse_args()
    table = json.loads(Path(args.table).read_text())
    gates = synthesize(**table)
    if gates is not None:
        if isinstance(gates, dict):
            Path(args.output).write_text(json.dumps(gates) + '\n')
        else:
            lines = [' '.join(map(str, gate)) for gate in gates]
            lines.append('out ' + str(gates[-1][0]))
            Path(args.output).write_text('\n'.join(lines) + '\n')
