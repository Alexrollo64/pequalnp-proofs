"""Reconstruct and verify the five 7-test tables beside RepeatedInput.lean."""
from pathlib import Path
import re

TESTS = [(2, 0), (2, 1), (3, 1), (3, 4), (4, 0), (4, 1), (4, 4)]


def table(free_input):
    # Each raw input costs one, except for the input that may be repeated.
    # Pattern zero is free. All costs are capped at seven.
    costs = [7] * 128
    costs[0] = 0
    for j in range(10):
        word = sum(1 << i for i, (r, c) in enumerate(TESTS) if j in (r, 5 + c))
        costs[word] = min(costs[word], int(j != free_input))

    # Close each budget under AND and OR, including combinations with a free word.
    for budget in range(7):
        while True:
            changed = False
            for a in range(128):
                for b in range(a):
                    if costs[a] + costs[b] > budget:
                        continue
                    for result in (a & b, a | b):
                        if costs[result] > budget:
                            costs[result] = budget
                            changed = True
            if not changed:
                break
    assert all(max(costs[a & b], costs[a | b]) <= costs[a] + costs[b]
               for a in range(128) for b in range(128))
    return sum(cost << (3 * word) for word, cost in enumerate(costs))


if __name__ == "__main__":
    source = Path(__file__).with_name("RepeatedInput.lean").read_text()
    digits = source.split("let table : Nat := ![", 1)[1].split("] s", 1)[0]
    expected = list(map(int, re.findall(r"[0-9]+", digits)))
    assert expected == [table(j) for j in (None, 2, 3, 5, 9)]
    print("Five tables reproduced. All 81,920 pairs satisfy both inequalities.")
