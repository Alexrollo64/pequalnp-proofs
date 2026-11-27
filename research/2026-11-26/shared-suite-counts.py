"""Enumerate the 36 first ORs and compute a smallest extension for this family."""
import json
import subprocess
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path

binary = Path(__file__).with_name("shared-suite").resolve()
tables = set()
successful = []
for a, b in product([2, 3, 4, 10, 11, 14], [7, 8, 9, 15, 16, 19]):
    run = subprocess.run([binary, str(a), str(b)], text=True, capture_output=True)
    if run.returncode == 1 and run.stdout.strip() == "no tail of at most 15 gates":
        continue
    run.check_returncode()
    header, *entries = run.stdout.splitlines()
    assert header == "tail 15"
    masks = set()
    for line in entries:
        weight, word = line.split()
        error = int(word, 16)
        assert error.bit_count() == int(weight)
        masks.add(error)
    successful.append({"pair": [a, b], "tables": len(masks)})
    tables.update(masks)

def cells(mask):
    return [i for i in range(100) if mask >> i & 1]

minimal = []
for mask in sorted(tables, key=lambda m: (m.bit_count(), m)):
    if not any((sub & mask) == sub for sub in minimal):
        minimal.append(mask)

@lru_cache(None)
def cover(masks):
    if not masks:
        return ()
    return min(((i,) + cover(tuple(m for m in masks if not (m >> i & 1)))
                for i in cells(masks[0])), key=len)

@lru_cache(None)
def packing(masks):
    if not masks:
        return ()
    first, *rest = masks
    with_first = (first,) + packing(tuple(m for m in rest if not m & first))
    return max(with_first, packing(tuple(rest)), key=len)

extra = cover(tuple(minimal))
disjoint = packing(tuple(minimal))
assert all(any(m >> i & 1 for i in extra) for m in tables)
assert all(not a & b for a, b in combinations(disjoint, 2))
assert len(disjoint) == len(extra)
print(json.dumps({"first_gates_tested": 36, "survivors": successful, "distinct_tables": len(tables),
                  "minimal_error_sets": list(map(cells, minimal)), "extra_cells": extra,
                  "disjoint_error_sets": list(map(cells, disjoint))}, indent=2))
