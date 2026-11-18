"""Exact small controls for Frobenius orbit determinants in characteristic three."""
from itertools import product
from random import Random

# Elements a+b*i of F9, i^2=-1, stored as a+3*b.
def add(a,b):
    return (a%3+b%3)%3+3*((a//3+b//3)%3)
def neg(a):
    return (-a%3)%3+3*((-(a//3))%3)
def mul(a,b):
    x,y = a%3,a//3
    u,v = b%3,b//3
    return (x*u-y*v)%3+3*((x*v+y*u)%3)
def frob(a):
    return a%3+3*((- (a//3))%3)
def det(cols):
    m=[list(r) for r in zip(*cols)]
    value=1
    for i in range(len(m)):
        j=next((j for j in range(i,len(m)) if m[j][i]),None)
        if j is None:
            return 0
        if j!=i:
            m[i],m[j]=m[j],m[i]
            value=neg(value)
        value=mul(value,m[i][i])
        inv=next(x for x in range(1,9) if mul(x,m[i][i])==1)
        for row in m[i+1:]:
            scale=mul(row[i],inv)
            for k in range(i,len(row)):
                row[k]=add(row[k],neg(mul(scale,m[i][k])))
    return value

def main():
    rng=Random(7919)
    counts=[0,0]
    # Compare determinants over the splitting field with the orbit-block
    # computation over the ground field, including singular matrices.
    factor=det([[1,3],[1,frob(3)]])
    assert factor and frob(factor)==neg(factor)
    for degrees in ((1,2),(2,2),(1,1,2,2),(2,2,2)):
        n=sum(degrees)
        for _ in range(128):
            raw=[]
            rational=[]
            scale=1
            for d in degrees:
                v=[rng.randrange(3 if d==1 else 9) for i in range(n)]
                raw.append(v)
                rational.append([a%3 for a in v])
                if d==2:
                    raw.append([frob(a) for a in v])
                    rational.append([a//3 for a in v])
                    scale=mul(scale,factor)
            a=det(raw)
            assert a==mul(det(rational),scale)
            assert frob(a)==(neg(a) if degrees.count(2)%2 else a)
            counts[bool(a)]+=1
    print("PASS: 512 determinant comparisons; singular/invertible =",counts)

if __name__=="__main__":
    main()
