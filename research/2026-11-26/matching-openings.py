"""Independent exhaustive witness count for two disjoint binary opening gates."""
from collections import Counter
from itertools import combinations, permutations, product

matchings = [sum(1 << (3*r+c) for r,c in enumerate(p)) for p in permutations(range(3))]
target = [any(x & m == m for m in matchings) for x in range(512)]
pivots = [[x for x in range(512) if not x & (1 << i) and target[x] != target[x ^ (1 << i)]]
          for i in range(9)]

def evaluate(pair, op, x):
    bits = [bool(x & (1 << i)) for i in pair]
    return all(bits) if op == 'AND' else any(bits)

def witnesses(left, right, a, b):
    result = {}
    for i, xs in enumerate(pivots):
        for x in xs:
            y = x ^ (1 << i)
            if evaluate(left,a,x) == evaluate(left,a,y) and evaluate(right,b,x) == evaluate(right,b,y):
                result[i] = (x,y)
                break
    return result

if __name__ == '__main__':
    counts = Counter()
    for left,right in combinations(combinations(range(9),2),2):
        if set(left) & set(right):
            continue
        for a,b in product(('AND','OR'), repeat=2):
            n = len(witnesses(left,right,a,b))
            counts[(a,b,n)] += 1
    assert sum(counts.values()) == 1512
    for k,v in sorted(counts.items()):
        print(*k,v)
