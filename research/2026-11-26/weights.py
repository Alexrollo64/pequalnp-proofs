"""Six assignments per deleted edge and a subadditive cost on six-bit truth tables."""
from itertools import permutations
from pathlib import Path

matchings = [sum(1 << (3*r+c) for r,c in enumerate(p)) for p in permutations(range(3))]
def pm(x):
    return any(x & m == m for m in matchings)

def samples(i):
    allowed = 511 ^ (1<<i)
    for x in matchings:
        if x & ~allowed:
            continue
        for y in range(512):
            if y & ~allowed or pm(y):
                continue
            common = [1 << j for j in range(9) if x & ~y & (1<<j) and pm(y | (1<<j))]
            if len(common) >= 2:
                p,q = common[:2]
                return [x, x^p, x^q, y, y|p, y|q]
    raise AssertionError(i)
def column(xs, fn):
    return sum(int(fn(x)) << n for n,x in enumerate(xs))
def costs():
    # Cap costs at 3: only the distinction between 2 and at least 3 is needed.
    w = [3]*64
    for a in (0,7,56,63): w[a]=0
    for a in (21,35): w[a]=1
    while True:
        before = w[:]
        for a in range(64):
            w[63-a]=min(w[63-a],w[a])
            for b in range(64):
                for c in (a|b,a&b): w[c]=min(w[c],w[a]+w[b])
        if before==w: return w
if __name__=='__main__':
    w=costs()
    for i in range(9):
        xs=samples(i)
        raw=[column(xs,lambda x: (x>>j)&1) for j in range(9)]
        assert raw[i]==0 and sum(w[a] for a in raw)==2 and w[column(xs,pm)]==3
        print(i,xs,raw)
    print('cost table (base 4)',sum(v<<(2*j) for j,v in enumerate(w)))
