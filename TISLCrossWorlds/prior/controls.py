"""Exact finite controls for block-sign assembly and the modified centroid pins."""
from itertools import product, permutations
import json
import random


def solvable_columns(columns, target):
    pivots = {}
    for v in columns:
        while v:
            k = v.bit_length()
            if k not in pivots:
                pivots[k] = v
                break
            v ^= pivots[k]
    while target:
        k = target.bit_length()
        if k not in pivots:
            return False
        target ^= pivots[k]
    return True


def block_tests():
    rng = random.Random(2341)
    tests = 0
    for n in range(1,6):
        for _ in range(500):
            source = [rng.randrange(3) for _ in range(n)]
            target = source[:]
            rng.shuffle(target)
            if rng.randrange(5)==0:
                target[rng.randrange(n)] = rng.randrange(3)
            dims = [rng.randrange(2) for _ in range(3)]
            free = [rng.randrange(2) for _ in range(3)]
            a = [rng.randrange(2) for _ in range(n)]
            b = [rng.randrange(2) for _ in range(n)]
            true_signs = set()
            ordinary = sorted(source)==sorted(target)
            for p in permutations(range(n)):
                if any(source[i]!=target[p[i]] for i in range(n)):
                    continue
                odd = [p[i] for i in range(n) if dims[source[i]]]
                sign = sum(x>y for j,x in enumerate(odd) for y in odd[j+1:]) % 2
                sign ^= sum(a[i]^b[p[i]] for i in range(n)) % 2
                true_signs.add(sign)
                if any(free[t] for t in source):
                    true_signs.add(sign^1)
            flexible = any(free[t] for t in source) or any(
                dims[t] and source.count(t)>1 for t in set(source)
            )
            for requested in range(2):
                if not ordinary:
                    got = False
                elif flexible:
                    got = True
                else:
                    odd = [target.index(t) for t in source if dims[t]]
                    perm = sum(x>y for j,x in enumerate(odd) for y in odd[j+1:]) % 2
                    col = [(1<<i)+(1<<(n+j))+((a[i]^b[j])<<(2*n))
                           for i,j in product(range(n),repeat=2) if source[i]==target[j]]
                    rhs = (1<<(2*n))-1 + ((requested^perm)<<(2*n))
                    got = solvable_columns(col,rhs)
                assert got==(requested in true_signs)
                tests += 1
    return tests


def centroid_dimension(beta, xdim, zdim):
    pivots = {}
    for i,j,k in product(range(xdim), range(xdim), range(zdim)):
        row={}
        for p in range(xdim):
            if k in beta.get((p,j),{}):
                row[p*xdim+i]=beta[p,j][k]
        for ell,c in beta.get((i,j),{}).items():
            row[xdim*xdim + k*zdim + ell]=(-c)%3
        while row:
            p=min(row)
            if p not in pivots:
                mult=pow(row[p],-1,3)
                pivots[p]={q:t*mult%3 for q,t in row.items()}
                break
            mult=row[p]
            for q,t in pivots[p].items():
                x=(row.get(q,0)-mult*t)%3
                if x:
                    row[q]=x
                else:
                    row.pop(q,None)
    return xdim*xdim+zdim*zdim-len(pivots)


def toy_carrier(pins, patched):
    # The two-coordinate edge slices here check the centroid proof only.
    # The paper uses larger trace edge blocks for its independent rank tags.
    b=pins+2
    m=b
    xdim=2*m+2*b
    zdim=pins+2+b
    values={}
    def setv(i,j,coords):
        assert (i,j) not in values
        values[i,j]=dict(coords)
        values[j,i]=dict(coords)
    setv(0,0,{0:1})
    setv(0,pins+1,{pins+1:1})
    for j in range(pins):
        setv(0,j+1,{0:1})
        setv(j+1,j+1,{1+j:1})
        if patched:
            setv((j+1)%pins+1,(j+2)%pins+1,{1+j:1})
    for i in range(m):
        setv(i,m+i,{pins+2+i:1})
    for j in range(b):
        t=2*m+2*j
        setv(t,t,{pins+2+j:1,pins+2+(j+1)%b:1})
        setv(t+1,t+1,{pins+2+j:1,pins+2+(j+1)%b:2})
    return centroid_dimension(values,xdim,zdim)

if __name__ == "__main__":
    cases={}
    for pins in (5,6,7):
        old=toy_carrier(pins,False)
        new=toy_carrier(pins,True)
        assert old==pins+1 and new==1
        cases[str(pins)]=[old,new]
    print(json.dumps({"block_assembly_profiles":block_tests(),
                      "toy_centroid_dimensions_before_after":cases},indent=2))
