"""Reproduce the weights embedded in Mask31917056Lower.lean."""
from itertools import product

CASES = [(2, 0), (2, 1), (3, 1), (3, 4), (4, 0), (4, 1), (4, 4)]
MASK = 31917056


def pattern(predicate):
    return sum(1 << i for i, (row, col) in enumerate(CASES) if predicate(row, col))


inputs = [pattern(lambda r, c: k == r or k == 5 + c) for k in range(10)]
target = pattern(lambda r, c: MASK >> (5 * r + c) & 1)

# A zero-pattern input is free on these seven tests. At each greater budget,
# close under one binary combination of two formulas with smaller budgets.
levels = [{0}, {0, *inputs}]
for budget in range(2, 7):
    values = levels[-1].copy()
    for left in range(1, budget // 2 + 1):
        for a, b in product(levels[left], levels[budget - left]):
            values.update([a & b, a | b])
    levels.append(values)

weights = [next((n for n, v in enumerate(levels) if x in v), 7) for x in range(128)]
for a, b in product(range(128), repeat=2):
    assert max(weights[a & b], weights[a | b]) <= weights[a] + weights[b]
assert target == 101 and weights[target] == 7
assert sum(weights[inputs[i]] for i in (2, 3, 4, 5, 6, 7, 8, 9)) == 6
print(sum(w << (3 * i) for i, w in enumerate(weights)))
