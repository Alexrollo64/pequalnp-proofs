"""Check every published baseline on all inputs in its one-per-side promise."""
import json
from pathlib import Path

root = Path(__file__).resolve().parent
records = json.loads((root / 'results.json').read_text())['records']
for record in records:
    rows = record['rows']
    columns = record['columns']
    values = [
        sum(1 << (u * columns + v)
            for u in range(rows) for v in range(columns)
            if index == u or index == rows + v)
        for index in range(rows + columns)
    ]
    output = None
    count = 0
    for line in (root / record['baseline_file']).read_text().splitlines():
        fields = line.split()
        if fields[0] == 'out':
            output = int(fields[1])
            continue
        index = int(fields[0])
        operation = fields[1]
        left, right = map(int, fields[2:])
        assert index == len(values)
        assert 0 <= left < index and 0 <= right < index
        assert operation in ('and', 'or')
        value = (values[left] & values[right]) if operation == 'and' else (values[left] | values[right])
        values.append(value)
        count += 1
    assert output is not None and 0 <= output < len(values)
    assert values[output] == record['target_mask'], record['unit']
    assert count == record['baseline_gates'], record['unit']
    print(record['unit'], count, 'gates; all promised inputs checked')
print('Verified', len(records), 'baseline circuits')
