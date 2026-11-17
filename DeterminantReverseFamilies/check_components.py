"""Compare the component parity assembly with all possible small matchings."""
from itertools import permutations, product
from random import Random

def span(columns):
    values = {0}
    for x in columns:
        values |= {x ^ y for y in values}
    return values

def inversion(bits):
    return sum(a > b for i,a in enumerate(bits) for b in bits[i+1:]) % 2

def rigid_sign(left, right, odd, x, y, flexible, eta):
    n = len(left)
    if sorted(left) != sorted(right):
        return False
    if any(flexible[i] for i in left) or any(odd[i] and left.count(i)>1 for i in left):
        return True
    target_odd = [j for j,t in enumerate(right) if odd[t]]
    perm = [next(j for j in target_odd if right[j]==t) for t in left if odd[t]]
    rhs = eta ^ inversion(perm)
    edges = [(1<<i) | (1<<(n+j)) | ((x[i]^y[j])<<(2*n))
             for i,t in enumerate(left) for j,u in enumerate(right) if t==u]
    wanted = ((1<<(2*n))-1) | (rhs<<(2*n))
    return wanted in span(edges)

def all_matchings(left, right, odd, x, y, flexible, eta):
    for perm in permutations(range(len(right))):
        if len(left)!=len(perm) or any(t!=right[j] for t,j in zip(left,perm)):
            continue
        ordinary_sign = inversion([j for t,j in zip(left,perm) if odd[t]])
        if any(flexible[t] for t in left):
            return True
        if (ordinary_sign + sum(x[i]^y[j] for i,j in enumerate(perm)) + eta)%2==0:
            return True
    return False

rng=Random(1117)
count=0
for n in range(7):
    for _ in range(160):
        left=[rng.randrange(4) for _ in range(n)]
        right=left.copy()
        rng.shuffle(right)
        if n and rng.randrange(7)==0:
            right[rng.randrange(n)]=rng.randrange(4)
        odd=[rng.randrange(2) for _ in range(4)]
        x=[rng.randrange(2) for _ in range(n)]
        y=[rng.randrange(2) for _ in range(n)]
        flexible=[int(rng.randrange(8)==0) for _ in range(4)]
        for eta in (0,1):
            assert rigid_sign(left,right,odd,x,y,flexible,eta)==all_matchings(left,right,odd,x,y,flexible,eta)
            count+=1
print("Component assembly checks:",count)
