"""Independently evaluate a matrix-product circuit on all 2^18 assignments."""
import argparse
import json
from pathlib import Path


def verify(circuit):
    cases = 1 << 18
    full = (1 << cases) - 1
    values = []
    for bit in range(18):
        width = 1 << bit
        pattern = ((1 << width) - 1) << width
        period = 2 * width
        while period < cases:
            pattern |= pattern << period
            period *= 2
        values.append(pattern)
    counts = {'and': 0, 'or': 0, 'not': 0}
    assert circuit['input_count'] == 18
    for gate in circuit['gates']:
        operation = gate['op']
        parents = gate['inputs']
        assert operation in counts
        assert len(parents) == (1 if operation == 'not' else 2)
        assert all(type(parent) is int and 0 <= parent < len(values) for parent in parents)
        counts[operation] += 1
        left = values[parents[0]]
        if operation == 'not':
            value = full ^ left
        elif operation == 'and':
            value = left & values[parents[1]]
        else:
            value = left | values[parents[1]]
        values.append(value)
    assert len(circuit['outputs']) == 9
    total_errors = 0
    wrong_assignments = 0
    outputs = []
    for output, wire in enumerate(circuit['outputs']):
        assert type(wire) is int and 0 <= wire < len(values)
        row, column = divmod(output, 3)
        expected = 0
        for k in range(3):
            expected |= values[3 * row + k] & values[9 + 3 * k + column]
        difference = expected ^ values[wire]
        errors = bin(difference).count('1')
        total_errors += errors
        wrong_assignments |= difference
        outputs.append({'output': output, 'wire': wire, 'errors': errors})
    size = len(circuit['gates'])
    return dict(input_assignments=cases,output_values_checked=9*cases,gates=size,
                gate_counts=counts,within_shard_6=(size <= 44 and counts['not'] == 1
                    and 23 <= counts['and'] <= 33),
                incorrect_output_values=total_errors,
                assignments_with_an_error=bin(wrong_assignments).count('1'),outputs=outputs)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('circuit')
    args = parser.parse_args()
    print(json.dumps(verify(json.loads(Path(args.circuit).read_text())),indent=2))
