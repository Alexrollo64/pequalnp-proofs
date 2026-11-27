"""Replay the explicit two-copy circuit on every promised input."""
import json
from pathlib import Path
root=Path(__file__).parent
def build():
    expr=json.loads((root/'two-copy-expression.json').read_text())
    gates=[('or',11,12),('or',20,13),('or',21,9)]
    def compile_tree(node):
        if node=='h':return 22
        if type(node) is int:
            assert 0<=node<20
            return node
        op,left,right=node
        assert op in ('or','and')
        a=compile_tree(left);b=compile_tree(right)
        gates.append((op,a,b))
        return 19+len(gates)
    out=compile_tree(expr)
    assert out==35 and len(gates)==16
    return gates,out
if __name__=='__main__':
    gates,out=build()
    positives=0
    for r in range(10):
        for c in range(10):
            w=[i in (r,c+10) for i in range(20)]
            for op,a,b in gates:w.append((w[a] and w[b]) if op=='and' else (w[a] or w[b]))
            expected=r//5==c//5 and bool(31917056 & (1<<(5*(r%5)+c%5)))
            assert w[out]==expected,(r,c)
            positives+=expected
    print(f'{len(gates)} gates; all 100 cells correct; {positives} positives')
