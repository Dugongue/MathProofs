"""Check the calibrated determinant-line identity over prime fields (stdlib)."""
from itertools import product
from random import Random

def identity(n):
    return [[int(i==j) for j in range(n)] for i in range(n)]

def trans(m):
    return list(map(list,zip(*m)))

def mult(m,n,p):
    return [[sum(a*b for a,b in zip(row,col))%p for col in zip(*n)] for row in m]

def rr(m,p):
    a=[row[:] for row in m]
    piv=[]
    value=1
    for j in range(len(a[0]) if a else 0):
        i=len(piv)
        k=next((k for k in range(i,len(a)) if a[k][j]%p),None)
        if k is None:
            continue
        if k!=i:
            a[k],a[i]=a[i],a[k]
            value=-value
        value=value*a[i][j]%p
        inv=pow(a[i][j],-1,p)
        a[i]=[x*inv%p for x in a[i]]
        for k,row in enumerate(a):
            if k!=i:
                v=row[j]
                a[k]=[(x-v*y)%p for x,y in zip(row,a[i])]
        piv.append(j)
    return a,piv,value%p

def det(m,p):
    _,piv,d=rr(m,p)
    return d if len(piv)==len(m) else 0

def inverse(m,p):
    n=len(m)
    rows,piv,_=rr([a+b for a,b in zip(m,identity(n))],p)
    assert piv==list(range(n))
    return [row[n:] for row in rows]

def normal(d,p):
    m,n=len(d),len(d[0])
    reduced,piv,_=rr(d,p)
    free=[j for j in range(n) if j not in piv]
    kcols=[]
    for j in free:
        v=identity(n)[j]
        for i,k in enumerate(piv):
            v[k]=-reduced[i][j]%p
        kcols.append(v)
    ell=trans(kcols+[identity(n)[j] for j in piv])
    cols=[trans(d)[j] for j in piv]+identity(m)
    _,keep,_=rr(trans(cols),p)
    em=trans([cols[i] for i in keep])
    rho=det(em,p)*pow(det(ell,p),-1,p)%p
    return ell,em,rho,len(free),len(piv)

def one(fmt,p,rng,zero):
    idx=list(product(*(range(d) for d in fmt)))
    locations={v:i for i,v in enumerate(idx)}
    g=[]
    for d in fmt:
        while True:
            a=[[rng.randrange(p) for _ in range(d)] for _ in range(d)]
            if det(a,p):
                g.append(a)
                break
    A=[[g[0][i][a]*g[1][j][b]*g[2][k][c]%p for a,b,c in idx] for i,j,k in idx]
    field_t=[[0 if zero else rng.randrange(p)] for _ in idx]
    def tangent(x):
        cols=[]
        for mode,d in enumerate(fmt):
            for i,j in product(range(d),repeat=2):
                v=[]
                for pos in idx:
                    arg=list(pos)
                    arg[mode]=j
                    v.append(x[locations[tuple(arg)]][0] if pos[mode]==i else 0)
                cols.append(v)
        return trans(cols)
    D=tangent(field_t)
    U=tangent(mult(A,field_t,p))
    units=[(mode,i,j) for mode,d in enumerate(fmt) for i,j in product(range(d),repeat=2)]
    inverses=[inverse(gm,p) for gm in g]
    H=[[g[u][a][i]*inverses[u][j][b]%p if u==v else 0
        for v,i,j in units] for u,a,b in units]
    assert mult(A,D,p)==mult(U,H,p)
    X,B,x,k,rank=normal(D,p)
    Y,C,y,k2,r2=normal(U,p)
    assert (k,rank)==(k2,r2)
    dom=mult(inverse(Y,p),mult(H,X,p),p)
    cod=mult(inverse(C,p),mult(A,B,p),p)
    dk=det([r[:k] for r in dom[:k]],p)
    dn=det([r[rank:] for r in cod[rank:]],p)
    return det(A,p)==y*pow(x,-1,p)*dn*pow(dk,-1,p)%p

def main():
    rng=Random(817723)
    tested=0
    for p,fmt,trial in product([3,5,7],[(1,2,3),(2,2,3),(2,3,3)],range(8)):
        assert one(fmt,p,rng,trial==0)
        tested+=1
    print("PASS:",tested,"tangent determinant comparisons including zero tensors.")

if __name__=="__main__":
    main()
