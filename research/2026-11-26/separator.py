"""Exact synthesis of a monotone separator with one use per leaf token."""
from functools import lru_cache
import sys, json

WIRES = (2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19)
CELLS = [sum(1<<i for i,w in enumerate(WIRES) if w in (p//10,10+p%10)) for p in range(100)]
POS = [p for p in range(100) if p//50 == p%10//5 and (31917056 >> (5*(p//10%5)+p%5))&1]
NEG = sorted(set(range(100))-set(POS))

def subset(a,b):
    return (a & ~b) == 0

def synthesis(s):
    outside=[i for i in range(16) if not s>>i&1]
    labels=[WIRES[i] for i in outside]+['h','h']
    def observation(x):
        v=sum(1<<j for j,i in enumerate(outside) if x>>i&1)
        if x&s:v|=3<<len(outside)
        return v
    def trim(rows):
        kept=[]
        for r in sorted(set(rows),key=int.bit_count):
            if not any(subset(x,r) for x in kept):kept.append(r)
        return tuple(sorted(kept))
    def solve(s,p,n):
        # Each pair must share a token true on the positive and false on the negative.
        return search(s,trim(x&s for x in p),trim(x&s for x in n))
    @lru_cache(None)
    def search(s,p,n):
        if not p:return 'false'
        if not n:return 'true'
        if any(not x&y for x in p for y in n):return None
        common=s
        for r in (*p,*n):common&=r
        if common:return labels[(common&-common).bit_length()-1]
        # A child receiving the row must distinguish it from every column.
        # Any inclusion-minimal pair difference suffices for this test.
        needs_p=[trim(x&y for y in n) for x in p]
        needs_n=[trim(x&y for x in p) for y in n]
        a=(s-1)&s
        while a:
            b=s^a
            if a<b:
                for op,rows,needs in [('or',p,needs_p),('and',n,needs_n)]:
                    left=[];right=[];either=[]
                    for row,requirements in zip(rows,needs):
                        la=all(a&t for t in requirements)
                        rb=all(b&t for t in requirements)
                        if la and rb:either.append(row)
                        elif la:left.append(row)
                        elif rb:right.append(row)
                        else:break
                    else:
                        def test(side,rs):
                            return solve(side,rs,n) if op=='or' else solve(side,p,rs)
                        if test(a,left) is None or test(b,right) is None:continue
                        def assign(i):
                            if i==len(either):
                                l=test(a,left);r=test(b,right)
                                if l is not None and r is not None:return [op,l,r]
                                return None
                            x=either[i]
                            for side,part in [(a,left),(b,right)]:
                                part.append(x)
                                v=assign(i+1) if test(side,part) is not None else None
                                part.pop()
                                if v is not None:return v
                            return None
                        result=assign(0)
                        if result is not None:return result
            a=(a-1)&s
        return None
    return solve((1<<len(labels))-1,[observation(CELLS[i]) for i in POS],
                 [~observation(CELLS[i]) for i in NEG])

if __name__=='__main__':
    print(json.dumps(synthesis(int(sys.argv[1]))))
