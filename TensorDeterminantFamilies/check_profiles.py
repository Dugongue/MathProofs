"""Exact small-field checks of lifting, basis twists and one neutral marker."""
from itertools import product

def det(A):
    A = [list(row) for row in A]
    d = 1
    for i in range(len(A)):
        p = next((j for j in range(i,len(A)) if A[j][i] % 3), None)
        if p is None:
            return 0
        if p != i:
            A[i],A[p] = A[p],A[i]
            d = -d
        v = A[i][i] % 3
        d = d*v % 3
        for j in range(i+1,len(A)):
            t = A[j][i]*v % 3
            A[j] = [(x-t*y)%3 for x,y in zip(A[j], A[i])]
    return d%3

def mm(a,b):
    return tuple(tuple(sum(x*y for x,y in zip(r,c))%3 for c in zip(*b)) for r in a)
def kron(a,b):
    return tuple(tuple(x*y%3 for x in r for y in s) for r in a for s in b)
def bit(x): return int(x==2)

G = []
for a,b,c,d in product(range(3), repeat=4):
    g=((a,b),(c,d))
    if det(g): G.append(g)
I=((1,0),(0,1))
R=((2,0),(0,1))
for target in (I,R):
    profile=set()
    for a,b,c in product(G,G,(1,2)):
        if tuple(tuple(c*x%3 for x in row) for row in mm(target,a))==b:
            profile.add((bit(det(a)),bit(det(b)),bit(c)))
    expected={(i,i^bit(det(target)),j) for i,j in product(range(2),repeat=2)}
    assert profile==expected
for refl in (0,1):
    profile=set()
    twist=tuple(tuple((2 if i==j==0 and refl else int(i==j)) for j in range(4)) for i in range(4))
    for a,b in product(G,repeat=2):
        middle=mm(twist,kron(a,b))
        profile.add((bit(det(a)),bit(det(middle)),bit(det(b))))
    assert profile=={(i,refl,j) for i,j in product(range(2),repeat=2)}

def mul(a,b):
    return tuple(sum(a[i]*b[k-i] for i in range(k+1))%3 for k in range(4))
one=(1,0,0,0)
for c,u,v in product((1,2),range(3),range(3)):
    t=(0,c,u,v)
    assert det((one,t,mul(t,t),mul(mul(t,t),t)))==1
for a in product(range(3),repeat=4):
    if a[0]:
        assert det([mul(a,tuple(int(j==i) for j in range(4))) for i in range(4)])==1
print("Passed two complete 2 x 2 x 1 transporter profiles, two complete 2 x 4 x 2 profiles via invertible middle flattenings, 18 automorphisms and 54 units of the marker algebra.")
