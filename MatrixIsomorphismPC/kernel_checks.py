"""Exact kernel-transport certificate identities; finite controls, not Lean verification."""
from itertools import combinations, permutations
from math import comb
from pathlib import Path
import hashlib
import json

ROOT=Path(__file__).resolve().parent

def add(*polys):
    out={}
    for p in polys:
        for mon,c in p.items():
            out[mon]=out.get(mon,0)+c
            if not out[mon]:del out[mon]
    return out

def scale(p,c):return {mon:a*c for mon,a in p.items() if a*c}
def mul(p,q):
    out={}
    for m,a in p.items():
        for n,b in q.items():
            mon=tuple(sorted(m+n));out[mon]=out.get(mon,0)+a*b
            if not out[mon]:del out[mon]
    return out

def sub(p,q):return add(p,scale(q,-1))
def cn(c):return {():c} if c else {}
def eye(n):return [[cn(int(i==j)) for j in range(n)] for i in range(n)]
def zero(m,n):return [[{} for j in range(n)] for i in range(m)]
def matmul(A,B):
    return [[add(*(mul(A[i][k],B[k][j]) for k in range(len(B)))) for j in range(len(B[0]))] for i in range(len(A))]
def matadd(*As):return [[add(*(A[i][j] for A in As)) for j in range(len(As[0][0]))] for i in range(len(As[0]))]
def matneg(A):return [[scale(p,-1) for p in row] for row in A]
def matdegree(A):return max((len(mon) for row in A for p in row for mon in p),default=0)
def parts(n,cap=None):
    if not n:yield ();return
    for k in range(min(n,cap or n),1-1,-1):
        for rest in parts(n-k,k):yield(k,)+rest

def jordan(part):
    n=sum(part);A=zero(n,n);off=0
    for l in part:
        for j in range(l-1):A[off+j][off+j+1]=cn(1)
        off+=l
    return A

def power(A,k):
    out=eye(len(A))
    for _ in range(k):out=matmul(out,A)
    return out

def kernel_first(A):
    n=len(A);ker=[j for j in range(n) if all(not A[i][j] for i in range(n))]
    perm=ker+[j for j in range(n) if j not in ker]
    return [[A[i][j] for j in perm] for i in perm],len(ker)

def certificate(pa,pb,k):
    n=sum(pa);A,a=kernel_first(power(jordan(pa),k));B,b=kernel_first(power(jordan(pb),k))
    X=[[{(i*n+j,):1} for j in range(n)] for i in range(n)]
    Y=[[{(n*n+i*n+j,):1} for j in range(n)] for i in range(n)]
    E=matadd(matmul(X,A),matneg(matmul(B,X)))
    F=matadd(matmul(X,Y),matneg(eye(n)))
    G=matadd(matmul(Y,X),matneg(eye(n)))
    # Inverse transport from source equations, not a new assumed constraint.
    H=matadd(matmul(matmul(Y,E),Y),matneg(matmul(matmul(G,A),Y)),matmul(matmul(Y,B),F))
    assert H==matadd(matmul(A,Y),matneg(matmul(Y,B)))
    assert matdegree(E)<=1 and matdegree(F)<=2 and matdegree(G)<=2
    terms=[];charged_degree=0
    for i in range(a):
        for j in range(n-b):
            r=b+j
            rows=[s for s in range(n) if B[s][r]]
            assert len(rows)==1
            # R_{j,i} = -E_{rows[0],i}.
            assert scale(E[rows[0]][i],-1)==X[r][i]
            terms.append(mul(Y[i][r],scale(E[rows[0]][i],-1)))
            charged_degree=max(charged_degree,2)
    for i in range(b):
        for j in range(n-a):
            r=a+j;rows=[s for s in range(n) if A[s][r]]
            assert len(rows)==1
            assert H[rows[0]][i]==Y[r][i]
            # Charge Q times full degree3 source expansion of H, despite cancellation.
            charged_degree=max(charged_degree,4)
            terms.append(scale(mul(X[i][r],H[rows[0]][i]),-1))
    terms.extend(scale(G[i][i],-1) for i in range(a))
    terms.extend(F[i][i] for i in range(b))
    result=add(*terms)
    assert result==cn(a-b),(pa,pb,k,result,a,b)
    return {'source_jordan':pa,'target_jordan':pb,'power':k,'nullities':[a,b],
            'nonzero_constant':a-b,'charged_degree_bound':max(2,charged_degree),
            'exact_certificate_identity':'PASS'}

def determinant(A):
    n=len(A);out={}
    for p in permutations(range(n)):
        inversions=sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))
        term=cn((-1)**inversions)
        for i,j in enumerate(p):term=mul(term,A[i][j])
        out=add(out,term)
    return out

def main():
    cases=[]
    for n in range(1,6):
        ps=list(parts(n))
        for pa in ps:
            for pb in ps:
                if pa==pb:continue
                for k in range(1,n+1):
                    a=sum(min(k,l) for l in pa);b=sum(min(k,l) for l in pb)
                    if a!=b:
                        cases.append(certificate(pa,pb,k));break
    assert cases
    detcases=[]
    for n in range(1,4):
        X=[[{(i*n+j,):1} for j in range(n)] for i in range(n)]
        Y=[[{(n*n+i*n+j,):1} for j in range(n)] for i in range(n)]
        assert determinant(matmul(X,Y))==mul(determinant(X),determinant(Y))
        detcases.append(n)
    lucas=0
    for p in [2,3,5,7,11]:
        for a in range(65):
            for b in range(65):
                if a==b:continue
                diff=abs(a-b);d=1
                while diff%p==0:diff//=p;d*=p
                assert d<=max(a,b)
                aa=comb(a,d) if d<=a else 0;bb=comb(b,d) if d<=b else 0
                assert (aa-bb)%p!=0
                lucas+=1
    receipt={'status':'PASS','scope':'Finite exact polynomial identities and digit controls; not the universal mathematical proof or a Lean certificate.',
             'kernel_certificate_cases':len(cases),'cases':cases,'determinant_identity_dimensions':detcases,
             'Lucas_first_differing_digit_cases':lucas,'code_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    (ROOT/'CHECKS.json').write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({k:v for k,v in receipt.items() if k!='cases'}))

if __name__=='__main__':main()
