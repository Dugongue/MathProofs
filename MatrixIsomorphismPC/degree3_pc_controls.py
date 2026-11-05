"""Exact, replayed sequential-PC controls, distinguished from NS degree."""
from pathlib import Path
from itertools import combinations_with_replacement
import json, hashlib, time
from checks import poly_add, poly_scale, poly_mul

def control(A,B,prime=101,bound=3):
    n=len(A);V=2*n*n;p=prime
    def const(k):return {():k%p} if k%p else {}
    def variable(k):return {(k,):1}
    def plus(xs):
        d={}
        for x in xs:d=poly_add(d,x,p)
        return d
    def mm(a,b):return [[plus([poly_mul(a[i][k],b[k][j],p) for k in range(len(b))]) for j in range(len(b[0]))] for i in range(len(a))]
    def minus(a,b):return [[poly_add(x,poly_scale(y,-1,p),p) for x,y in zip(r,s)] for r,s in zip(a,b)]
    X=[[variable(i*n+j) for j in range(n)] for i in range(n)]
    Y=[[variable(n*n+i*n+j) for j in range(n)] for i in range(n)]
    Xt=[list(r) for r in zip(*X)]
    Ac=[[const(x) for x in r] for r in A];Bc=[[const(x) for x in r] for r in B]
    I=[[const(int(i==j)) for j in range(n)] for i in range(n)]
    sources=[v for M in [minus(mm(mm(X,Ac),Xt),Bc),minus(mm(X,Y),I),minus(mm(Y,X),I)] for r in M for v in r if v]
    basis={};lines=[];events=[];queue=[]
    def derive(candidate,origin):
        q=dict(candidate);steps=[]
        while q:
            pivot=max(q,key=lambda m:(len(m),m))
            if pivot not in basis:
                inv=pow(q[pivot],-1,p);q=poly_scale(q,inv,p)
                lid=len(lines);lines.append(q);events.append({'origin':origin,'subtract':steps,'normalize':inv,'line':[[list(m),c] for m,c in q.items()]});basis[pivot]=lid
                if len(pivot)<bound:queue.append(lid)
                return pivot==()
            lid=basis[pivot];factor=q[pivot];steps.append([lid,factor]);q=poly_add(q,poly_scale(lines[lid],-factor,p),p)
        return False
    found=False
    for i,s in enumerate(sources):
        if derive(s,{'source':i}):found=True;break
    qi=0
    while not found and qi<len(queue):
        lid=queue[qi];qi+=1
        for v in range(V):
            if derive(poly_mul(lines[lid],{(v,):1},p),{'multiply_line':lid,'variable':v}):found=True;break
    assert found,'No PC refutation at requested bound'
    replay=[];maximum=0
    for event in events:
        origin=event['origin']
        q=sources[origin['source']] if 'source' in origin else poly_mul(replay[origin['multiply_line']],{(origin['variable'],):1},p)
        maximum=max(maximum,max(map(len,q),default=0));assert maximum<=bound
        for lid,c in event['subtract']:
            assert lid<len(replay);q=poly_add(q,poly_scale(replay[lid],-c,p),p)
            assert max(map(len,q),default=0)<=bound
        q=poly_scale(q,event['normalize'],p);assert q=={tuple(m):c for m,c in event['line']};replay.append(q)
    assert replay[-1]=={():1}
    return {'A':A,'B':B,'prime':prime,'bound':bound,'maximum_actual_line_degree':maximum,'basis_lines':len(lines),'events':events,'replayed':True}

if __name__=='__main__':
    start=time.time()
    cases=[control([[0,1],[-2,0]],[[0,1],[-3,0]]),control([[0,1],[-1,0]],[[1,0],[0,1]])]
    p=Path(__file__).parent;f=p/'PROOF.md'
    out={'status':'PASS_EXACT_REPLAYED_SEQUENTIAL_PC_CONTROLS','refinement_sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'cases':cases,'elapsed_seconds':time.time()-start,'scope':'Finite control, not optimal-degree evidence or universal proof.'}
    (p/'PC-DEGREE3-CONTROLS.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(json.dumps({'status':out['status'],'elapsed_seconds':out['elapsed_seconds'],'cases':[{k:v for k,v in c.items() if k!='events'} for c in cases]},indent=2))
