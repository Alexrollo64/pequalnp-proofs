"""Find 16-gate candidates with CaDiCaL; independently check all 100 promises."""
import argparse
from itertools import combinations
from pathlib import Path
import json
import subprocess
import tempfile

RAW = [2,3,4,7,8,9,10,11,12,13,14,15,16,17,18,19]
START = [20,34,44,75,89,99]
def target(cell):
    r,c = divmod(cell,10)
    return r//5 == c//5 and bool(31917056 & (1 << (5*(r%5)+c%5)))

def search(cases, solver, seconds):
    clauses=[]
    last=0
    def variables(n):
        nonlocal last
        last+=n
        return list(range(last-n+1,last+1))
    def one(opts):
        clauses.append(opts)
        clauses.extend([-a,-b] for a,b in combinations(opts,2))
    gates=[]
    refs={i:[] for i in RAW + list(range(20,36))}
    signals={}
    for i in RAW:
        for p in cases:
            v=variables(1)[0]
            signals[i,p]=v
            r,c=divmod(p,10)
            clauses.append([v if i in (r,10+c) else -v])
    for w in range(20,36):
        src=RAW+list(range(20,w))
        left,right=variables(len(src)),variables(len(src))
        one(left); one(right)
        op=variables(1)[0]  # true = AND
        gates.append((src,left,right,op))
        for j,i in enumerate(src):
            refs[i].extend([left[j],right[j]])
            for k in range(j+1):
                clauses.append([-left[j],-right[k]])
            for k in range(j+1,len(RAW)):
                h=src[k]
                if i<20 and not any(target(p) and {i,h}=={p//10,10+p%10} for p in range(100)):
                    clauses.append([-op,-left[j],-right[k]])
        for p in cases:
            a,b,z=variables(3)
            signals[w,p]=z
            for j,i in enumerate(src):
                x=signals[i,p]
                for sel,y in ((left[j],a),(right[j],b)):
                    clauses.extend([[-sel,-x,y],[-sel,x,-y]])
            clauses.extend([[-op,-z,a],[-op,-z,b],[-op,z,-a,-b],
                            [op,z,-a],[op,z,-b],[op,-z,a,b]])
            if w==35: clauses.append([z if target(p) else -z])
    clauses.extend(v for i,v in refs.items() if i!=35)
    with tempfile.TemporaryDirectory() as directory:
        cnf=Path(directory)/"problem.cnf"
        with cnf.open('w') as f:
            print('p cnf',last,len(clauses),file=f)
            for c in clauses: print(*c,0,file=f)
        proc=subprocess.run([solver,'-q','-t',str(seconds),str(cnf)],capture_output=True,text=True)
    if proc.returncode not in (0,10,20): raise RuntimeError(proc.stderr or proc.stdout)
    if proc.returncode!=10: return ('UNSAT' if proc.returncode==20 else 'UNKNOWN'),None
    pos={int(v) for line in proc.stdout.splitlines() if line.startswith('v ') for v in line.split()[1:] if int(v)>0}
    return 'SAT',[(op in pos,src[next(j for j,v in enumerate(l) if v in pos)],
                       src[next(j for j,v in enumerate(r) if v in pos)]) for src,l,r,op in gates]

def errors(gates):
    wrong=[]
    for p in range(100):
        r,c=divmod(p,10)
        w=[i in (r,10+c) for i in range(20)]
        for is_and,a,b in gates: w.append((w[a] and w[b]) if is_and else (w[a] or w[b]))
        if w[-1]!=target(p): wrong.append(p)
    return wrong

if __name__=='__main__':
    cli=argparse.ArgumentParser()
    cli.add_argument('solver')
    cli.add_argument('--seconds',type=int,default=12)
    cli.add_argument('--cases',nargs='+',type=int,default=START)
    opt=cli.parse_args()
    cases=sorted(set(opt.cases))
    while True:
        status,gates=search(cases,opt.solver,opt.seconds)
        wrong=errors(gates) if gates else None
        assert wrong is None or set(cases).isdisjoint(wrong)
        print(json.dumps(dict(cases=cases,status=status,gates=gates,errors=wrong)),flush=True)
        if not wrong: break
        cases=sorted(set(cases)|{wrong[0]})
