"""Exact controls for the truncated principal-determinant polynomial over F3[t]/(t^k)."""
from itertools import combinations, permutations
import json
from random import Random


def add(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))


def mul(a,b):
    return tuple(sum(a[i]*b[d-i] for i in range(d+1))%3 for d in range(len(a)))


def minus(a):
    return tuple((-x)%3 for x in a)


def p_add(a,b,zero):
    out=[zero]*max(len(a),len(b))
    for l in (a,b):
        for i,c in enumerate(l):
            out[i]=add(out[i],c)
    while out and out[-1]==zero:
        out.pop()
    return out


def p_mul(a,b,zero):
    out=[zero]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[i+j]=add(out[i+j],mul(x,y))
    while out and out[-1]==zero:
        out.pop()
    return out


def detpoly(matrix,zero,one):
    n=len(matrix)
    out=[]
    for perm in permutations(range(n)):
        term=[one]
        for i,j in enumerate(perm):
            term=p_mul(term,matrix[i][j],zero)
        if sum(x>y for i,x in enumerate(perm) for y in perm[i+1:])%2:
            term=list(map(minus,term))
        out=p_add(out,term,zero)
    return out


def ring_det(matrix,zero,one):
    value=detpoly([[[x] for x in row] for row in matrix],zero,one)
    return value[0] if value else zero


def mm(a,b,zero):
    out=[]
    for row in a:
        ans=[]
        for col in zip(*b):
            v=zero
            for x,y in zip(row,col):
                v=add(v,mul(x,y))
            ans.append(v)
        out.append(ans)
    return out


def principal_polynomial(a,b,r,zero,one):
    # S = c*a + b. Choose rows and columns directly in its permutation expansion.
    # It is the coefficient shift of the n-degree determinant after cancelling c^(n-r).
    n=len(a)
    out=detpoly([[[b[i][j],a[i][j]] for j in range(n)] for i in range(n)],zero,one)
    assert all(c==zero for c in out[:n-r])
    return out[n-r:]


def direct_P(N,r,zero,one):
    n=len(N)
    out=[zero]*(r+1)
    out[r]=one
    for j in range(1,r+1):
        z=zero
        for idx in combinations(range(n),j):
            z=add(z,ring_det([[N[p][q] for q in idx] for p in idx],zero,one))
        out[r-j]=z
    return out


def sample_cases():
    rng=Random(47)
    checked=0
    for k in range(2,6):
        one=(1,)+(0,)*(k-1)
        zero=(0,)*k
        for n in range(1,5):
            I=[[one if i==j else zero for j in range(n)] for i in range(n)]
            r=min(n,k-1)
            for _ in range(24):
                G0=[list(row) for row in I]
                inverse=[list(row) for row in I]
                if n>1:
                    # g0 = D E where E is an upper elementary shear.
                    G0[0][1]=one
                    inverse[0][1]=minus(one)
                if rng.randrange(2):
                    negD=[list(row) for row in I]
                    negD[0][0]=minus(one)
                    G0=mm(negD,G0,zero)
                    inverse=mm(inverse,negD,zero)
                G=[[add(G0[i][j],(0,)+tuple(rng.randrange(3) for _ in range(k-1)))
                    for j in range(n)] for i in range(n)]
                N=[[(0,)+tuple(rng.randrange(3) for _ in range(k-1))
                    for _ in range(n)] for _ in range(n)]
                newA=mm(G,inverse,zero)
                newB=mm(mm(G,N,zero),inverse,zero)
                assert all(x[0]==int(i==j) for i,row in enumerate(newA) for j,x in enumerate(row))
                assert all(x[0]==0 for row in newB for x in row)
                old=direct_P(N,r,zero,one)
                assert principal_polynomial(I,N,r,zero,one)==old
                rho=mul(ring_det(G,zero,one),ring_det(inverse,zero,one))
                assert rho[0]==1
                assert principal_polynomial(newA,newB,r,zero,one)==[mul(rho,x) for x in old]
                checked+=1
    return checked


if __name__=="__main__":
    print(json.dumps({"formal_univariate_principal_covariance_cases":sample_cases()},indent=2))
