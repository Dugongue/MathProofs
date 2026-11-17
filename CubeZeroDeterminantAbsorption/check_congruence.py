"""Small exact checks of the mixed-transpose congruence reduction."""
from itertools import product
from random import Random

P = 3

def transpose(A):
    return tuple(zip(*A))

def mul(A, B):
    return tuple(tuple(sum(a*b for a,b in zip(row,col))%P for col in zip(*B)) for row in A)

def det(A):
    return (A[0][0]*A[1][1]-A[0][1]*A[1][0])%P

def inv(A):
    a,b=A[0]
    c,d=A[1]
    s=det(A)
    return ((s*d%P,-s*b%P),(-s*c%P,s*a%P))

mats=[((a,b),(c,d)) for a,b,c,d in product(range(P),repeat=4)]
group=[A for A in mats if det(A)]
rng=Random(17)
checked=0
for step in range(40):
    source=[rng.choice(mats),rng.choice(mats)]
    if step%2:
        ref=rng.choice(group)
        target=[mul(mul(transpose(ref),B),ref) for B in source]
    else:
        target=[rng.choice(mats),rng.choice(mats)]
    B=source+[transpose(A) for A in source]
    C=target+[transpose(A) for A in target]
    brute={g for g in group if all(mul(mul(transpose(g),b),g)==c for b,c in zip(B,C))}
    pairs=((p,q) for p,q in product(group,repeat=2)
           if all(mul(mul(transpose(p),b),q)==c for b,c in zip(B,C)))
    pair=next(pairs,None)
    if pair is None:
        assert not brute
        continue
    p,q=pair
    D=mul(q,inv(p))
    assert all(mul(transpose(D),b)==mul(b,D) for b in B)
    restored=set()
    for z in group:
        z_star=mul(D,inv(z))
        if all(mul(transpose(z_star),b)==mul(b,z) for b in B):
            restored.add(mul(z,p))
    assert brute==restored
    checked+=1
print("40 mixed tuple checks, reference-equivalence cases:",checked)
