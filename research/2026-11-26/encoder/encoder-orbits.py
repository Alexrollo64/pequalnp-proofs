from itertools import permutations, product, combinations
from pathlib import Path
from multiprocessing import Pool
import sys, json, subprocess, time, argparse
from pysat.solvers import Solver
from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool

faces={sum(1<<p for p in range(16) if (p>>j)&1==b) for j in range(4) for b in (0,1)}
inputs={1<<p for p in range(16)}
regular={sum(1<<p for p in range(16) if all(v==2 or (p>>j)&1==v for j,v in enumerate(pattern))) for pattern in product(range(3),repeat=4)}
regular.discard(65535)
candidates={(a|b) for a,b in combinations(regular,2)}-regular-{65535,0}
def transforms():
    for perm in permutations(range(4)):
        for flip in range(16):
            yield [sum(((x>>i)&1)<<j for i,j in enumerate(perm))^flip for x in range(16)]
maps=list(transforms())
def transform(mask,m):
    return sum(1<<m[i] for i in range(16) if (mask>>i)&1)
def orbit_reps():
    left=set(candidates);reps=[]
    while left:
        rep=min(left);orb={transform(rep,m) for m in maps}
        assert orb<=candidates
        reps.append((rep,len(orb)));left-=orb
    return reps
def encode(extra,budget):
    masks=set(regular)|set(extra)
    ids=IDPool(); c=CNF(); x={s:ids.id(('x',s)) for s in sorted(masks)}
    rules={s:[] for s in sorted(masks-inputs)}
    for a,b in combinations(sorted(masks),2):
        for t,op in ((a|b,'or'),(a&b,'and')):
            if t in rules and t!=a and t!=b:rules[t].append((ids.id((a,b,t)),a,b,op))
    for s,opt in rules.items():
        c.append([-x[s]]+[g for g,a,b,o in opt])
        for g,a,b,o in opt:
            for h in (s,a,b):c.append([-g,x[h]])
    for s in sorted(faces|inputs):c.append([x[s]])
    for cl in CardEnc.atmost([x[s] for s in rules],budget,vpool=ids,encoding=EncType.totalizer).clauses:c.append(cl)
    depth=budget
    ranks={(s,d):ids.id(('r',s,d)) for s in sorted(masks) for d in range(depth+1)}
    for s in sorted(masks):
        if s in inputs:
            for d in range(depth+1):c.append([ranks[s,d]])
        else:
            c.append([-ranks[s,0]]);c.append([-x[s],ranks[s,depth]])
            for d in range(1,depth+1):
                c.append([-ranks[s,d-1],ranks[s,d]])
                for g,a,b,_ in rules[s]:
                    c.append([-g,-ranks[s,d],ranks[a,d-1]]);c.append([-g,-ranks[s,d],ranks[b,d-1]])
    return c,x,rules
def run_one(args):
    extra,budget,checker,certdir=args
    c,x,rules=encode(extra,budget)
    with Solver(name='cadical195',bootstrap_with=c,with_proof=bool(checker)) as s:
        if s.solve():
            model=set(s.get_model());sel={u for u in x if x[u] in model};made=set(inputs);ordered=[]
            while not faces<=made:
                prev=len(made)
                for t in sorted(sel-made):
                    for _,a,b,op in rules[t]:
                        if a in made and b in made:
                            made.add(t);ordered.append([t,a,b,op]);break
                assert len(made)>prev
            return list(extra),'SAT',ordered
        if checker:
            base=Path(certdir)/('case-'+'-'.join(map(str,extra)))
            c.to_file(str(base)+'.cnf')
            proof=s.get_proof();assert proof and proof[-1].strip()=='0'
            Path(str(base)+'.drat').write_text('\n'.join(proof)+'\n')
            out=subprocess.run([checker,str(base)+'.cnf',str(base)+'.drat'],capture_output=True,check=True)
            assert b's VERIFIED' in out.stdout
        return list(extra),'UNSAT',None
def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--checker',default=None)
    ap.add_argument('--certdir',default='.')
    ap.add_argument('--jobs',type=int,default=2)
    opts=ap.parse_args()
    reps=orbit_reps();print('regular masks',len(regular),'possible first irregular masks',len(candidates),'symmetry classes',len(reps),flush=True)
    Path(opts.certdir).mkdir(exist_ok=True,parents=True)
    jobs=[((x,),31,opts.checker,opts.certdir) for x,_ in reps]
    with Pool(opts.jobs) as p:
        for rep,status,wit in p.imap_unordered(run_one,jobs):
            print(rep,status,'checked' if opts.checker and status=='UNSAT' else '',json.dumps(wit) if wit else '',flush=True)
if __name__=='__main__':main()

