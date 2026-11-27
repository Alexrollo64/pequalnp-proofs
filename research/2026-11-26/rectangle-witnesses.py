"""Minimum formula size for ORs of nonempty rectangles on a 10 by 10 promise."""
from functools import lru_cache
from itertools import combinations
import json

def present(n):
    return [i for i in range(n.bit_length()) if n >> i & 1]

def subsets(values):
    for length in range(1, len(values)+1):
        yield from combinations(values, length)

def cover(edges):
    # Rectangle costs add; the resulting formula has sum(costs) - 1 gates.
    by_cell = {i: [] for i in present(edges)}
    rows = sorted({i//10 for i in by_cell})
    for rs in subsets(rows):
        columns = [c for c in range(10) if all(10*r+c in by_cell for r in rs)]
        for cs in subsets(columns):
            rect = sum(1 << (10*r+c) for r in rs for c in cs)
            for cell in present(rect):
                by_cell[cell].append((rect, rs, cs))

    @lru_cache(None)
    def solve(left):
        if not left:
            return 0, ()
        cell = min(present(left), key=lambda i: len(by_cell[i]))
        return min((cost + len(rs) + len(cs), ((rs, cs),) + others)
                   for rect, rs, cs in by_cell[cell]
                   for cost, others in [solve(left & ~rect)])
    return solve(edges)

if __name__ == "__main__":
    target = sum(1 << (10*r+c) for r in range(10) for c in range(10)
                 if r//5 == c//5 and (31917056 >> (5*(r%5)+c%5)) & 1)
    found = {}
    for i in range(100):
        cost, rects = cover(target ^ (1 << i))
        if cost <= 17:
            found[str(i)] = rects
    print(json.dumps(found))
