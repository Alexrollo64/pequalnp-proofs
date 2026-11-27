"""Check the shared-edge witness census and an obstruction after deleting that edge."""
from collections import Counter
from itertools import combinations, permutations, product

matchings = [sum(1 << (3*r+c) for r,c in enumerate(p)) for p in permutations(range(3))]
values = [any(x & m == m for m in matchings) for x in range(512)]
def wire(x,i):
    return (x >> i) & 1

def output(x,i,j,is_or):
    return (wire(x,i) | wire(x,j)) if is_or else (wire(x,i) & wire(x,j))

def check():
    counts = Counter()
    for i in range(9):
        partners = [j for j in range(9) if i != j]
        for j,k in combinations(partners,2):
            for a,b in product([False,True],repeat=2):
                summaries = [(output(x,i,j,a),output(x,i,k,b)) for x in range(512)]
                hidden = [e for e in range(9) if not any(
                    summaries[x] == summaries[x^(1<<e)] and values[x] != values[x^(1<<e)]
                    for x in range(512))]
                blocked = not (a or b) and all(wire(m,j) or wire(m,k) for m in matchings if wire(m,i))
                assert hidden == ([i] if blocked else [])
                counts[a,b,len(hidden)] += 1
        allowed = [x for x in range(512) if not wire(x,i)]
        # Minimal accepting input and maximal rejecting input after setting edge i to zero.
        def obstruction():
            for x in allowed:
                if not values[x] or any(values[x^(1<<e)] for e in partners if wire(x,e)):
                    continue
                for y in allowed:
                    if values[y] or any(not values[y^(1<<e)] for e in partners if not wire(y,e)):
                        continue
                    if (x & ~y).bit_count() >= 2:
                        return x,y
        assert obstruction() is not None
    assert sum(counts.values()) == 1008
    return counts

if __name__ == '__main__':
    for (a,b,h),n in sorted(check().items()):
        print(('AND','OR')[a],('AND','OR')[b],h,n)
