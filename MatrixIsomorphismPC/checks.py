"""Bounded exact controls; not a proof of the universal theorem."""
from pathlib import Path
from itertools import combinations_with_replacement
import random, json, hashlib, time

def add(A,B): return [[x+y for x,y in zip(a,b)] for a,b in zip(A,B)]
def neg(A): return [[-x for x in a] for a in A]
def sub(A,B): return add(A,neg(B))
def mul(A,B): return [[sum(x*y for x,y in zip(a,b)) for b in zip(*B)] for a in A]
def tr(A): return [list(a) for a in zip(*A)]
def eye(n): return [[int(i==j) for j in range(n)] for i in range(n)]
rng=random.Random(20261104)
def mat(n,m): return [[rng.randrange(-3,4) for _ in range(m)] for _ in range(n)]

def poly_add(a,b,p):
    c=dict(a)
    for m,x in b.items():
        v=(c.get(m,0)+x)%p
        if v:c[m]=v
        else:c.pop(m,None)
    return c
def poly_scale(a,k,p): return {m:x*k%p for m,x in a.items() if x*k%p}
def poly_mul(a,b,p):
    c={}
    for m,x in a.items():
        for n,y in b.items():
            v=tuple(sorted(m+n));c[v]=(c.get(v,0)+x*y)%p
    return {m:x for m,x in c.items() if x}

def ns_control(A,B,mode,p=101,degree=4):
    n=len(A);V=2*n*n
    def var(k):return {(k,):1}
    def const(x):return {():x%p} if x%p else {}
    X=[[var(i*n+j) for j in range(n)] for i in range(n)]
    Y=[[var(n*n+i*n+j) for j in range(n)] for i in range(n)]
    def mm(A,B):
        return [[sum_poly([poly_mul(A[i][k],B[k][j],p) for k in range(len(B))]) for j in range(len(B[0]))] for i in range(len(A))]
    def sum_poly(xs):
        c={}
        for a in xs:c=poly_add(c,a,p)
        return c
    def cm(A):return [[const(x) for x in a] for a in A]
    def minus(A,B):return [[poly_add(a,poly_scale(b,-1,p),p) for a,b in zip(x,y)] for x,y in zip(A,B)]
    E=minus(mm(mm(X,cm(A)),tr(X)),cm(B)) if mode=='congruence' else minus(mm(X,cm(A)),mm(cm(B),X))
    F=minus(mm(X,Y),cm(eye(n)));G=minus(mm(Y,X),cm(eye(n)))
    sources=[v for M in [E,F,G] for row in M for v in row if v]
    products=[];basis={};certificate=None
    for si,s in enumerate(sources):
        sd=max(map(len,s))
        for d in range(degree-sd+1):
            for mon in combinations_with_replacement(range(V),d):
                prod=poly_mul({mon:1},s,p);ci=len(products);products.append((si,mon,prod))
                v=dict(prod);rep={ci:1}
                while v:
                    pivot=max(v,key=lambda x:(len(x),x))
                    if pivot not in basis:
                        inv=pow(v[pivot],-1,p);v=poly_scale(v,inv,p);rep={k:x*inv%p for k,x in rep.items() if x*inv%p};basis[pivot]=(v,rep)
                        if pivot==():certificate=rep
                        break
                    bv,br=basis[pivot];k=v[pivot]
                    v=poly_add(v,poly_scale(bv,-k,p),p)
                    for j,x in br.items():
                        val=(rep.get(j,0)-k*x)%p
                        if val:rep[j]=val
                        else:rep.pop(j,None)
                if certificate is not None:break
            if certificate is not None:break
        if certificate is not None:break
    assert certificate is not None, (mode,A,B,'no certificate within bound')
    result={}
    for j,c in certificate.items():result=poly_add(result,poly_scale(products[j][2],c,p),p)
    assert result=={():1}
    terms=[{'source':products[j][0],'multiplier':products[j][1],'coefficient':c} for j,c in certificate.items()]
    return {'mode':mode,'A':A,'B':B,'prime':p,'degree':degree,'source_count':len(sources),'products_considered':len(products),'certificate_terms':terms,'certificate_replayed':True}

def main():
    start=time.time();checks=0
    for _ in range(400):
        n=rng.randrange(1,5);A=mat(n,n);B=mat(n,n);X=mat(n,n);Y=mat(n,n)
        C=sub(mul(mul(X,A),tr(X)),B);G=sub(mul(Y,X),eye(n))
        L=sub(mul(X,A),mul(B,tr(Y)));K=sub(mul(Y,B),mul(A,tr(X)))
        assert L==sub(mul(C,tr(Y)),mul(mul(X,A),tr(G)))
        assert K==sub(mul(mul(G,A),tr(X)),mul(Y,C))
        # Exact residual commutator expansion, with arbitrary matrices.
        s,t,s0,t0=[mat(n,n) for _ in range(4)]
        u=sub(t,t0);v=sub(s,s0)
        lhs=sub(sub(mul(s,t),mul(t,s)),sub(mul(s0,t0),mul(t0,s0)))
        rhs=sub(sub(add(mul(v,t),mul(s0,u)),mul(u,s)),mul(t0,v))
        assert lhs==rhs;checks+=3
    for _ in range(200):
        mt,nt,mh,nh=[rng.randrange(1,5) for _ in range(4)]
        M=mat(mh,mt);N=mat(nh,nt);Tt=mat(nt,mt);Th=mat(nh,mh);St=mat(mt,nt);Sh=mat(mh,nh)
        E=sub(mul(Th,M),mul(N,Tt));Gh=sub(mul(Sh,Th),eye(mh));Ft=sub(mul(Tt,St),eye(nt))
        lhs=sub(mul(M,St),mul(Sh,N))
        rhs=add(sub(mul(mul(Sh,E),St),mul(mul(Gh,M),St)),mul(mul(Sh,N),Ft))
        assert lhs==rhs;checks+=1
    # Characteristic-safe polynomial square roots, without factorial divisions.
    hensel=[]
    for prime in [3,5,7,101]:
        for order in [2,3,5,8]:
            coeff=[1]
            for k in range(1,order):
                rhs=int(k==1)-sum(coeff[i]*coeff[k-i] for i in range(1,k))
                coeff.append(rhs*pow(2,-1,prime)%prime)
            for k in range(order):
                assert sum(coeff[i]*coeff[k-i] for i in range(k+1))%prime==int(k<=1)
            hensel.append({'prime':prime,'order':order,'coefficients':coeff})
    certificates=[
        ns_control([[0,1],[0,0]],[[0,0],[0,0]],'conjugacy'),
        ns_control([[0,1],[-2,0]],[[0,1],[-3,0]],'congruence'),
        ns_control([[0,1],[-1,0]],[[1,0],[0,1]],'congruence'),
    ]
    proof=Path(__file__).with_name('TRACE-CERTIFICATE.md')
    out={'status':'PASS_EXACT_FINITE_CONTROLS','proof_sha256':hashlib.sha256(proof.read_bytes()).hexdigest(),'integer_matrix_identity_checks':checks,'hensel_controls':hensel,'finite_field_NS_certificates':certificates,'elapsed_seconds':time.time()-start,'scope':'Controls corroborate identities/degree feasibility; universal proof and novelty require separate mathematical audit.'}
    Path(__file__).with_name('UNIVERSAL-INTERTWINER-CONTROLS.json').write_text(json.dumps(out,indent=2),encoding='utf8')
    print(json.dumps({k:v for k,v in out.items() if k not in ['hensel_controls','finite_field_NS_certificates']},indent=2))
    print([(c['mode'],len(c['certificate_terms'])) for c in certificates])
if __name__=='__main__':main()
