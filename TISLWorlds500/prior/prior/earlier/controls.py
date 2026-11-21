"""Finite controls for the regular cube-zero normal form and tuple threshold."""

from itertools import combinations_with_replacement, product
import json
from random import Random


def symprod(x, y):
    return tuple((x[i]*y[j] + (x[j]*y[i] if i != j else 0)) % 3
                 for i, j in combinations_with_replacement(range(len(x)), 2))


def vadd(x, y):
    return tuple((a+b) % 3 for a, b in zip(x, y))


def acts_by_radical(node, vector):
    x, z = node
    a = vector[0]
    y = vector[1:1+len(x)]
    return (0,) + tuple(a*i % 3 for i in x) + vadd(
        tuple(a*j % 3 for j in z), symprod(x, y)
    )


def rank(rows, width):
    a = [list(r) for r in rows]
    h = 0
    for j in range(width):
        k = next((k for k in range(h, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[h], a[k] = a[k], a[h]
        t = pow(a[h][j], -1, 3)
        a[h] = [t*x % 3 for x in a[h]]
        for k in range(h+1, len(a)):
            t = a[k][j]
            if t:
                a[k] = [(b-t*c) % 3 for b,c in zip(a[k], a[h])]
        h += 1
    return h


def nonzero_line(n, nodes):
    zdim = n*(n+1)//2
    ambient = 1+n+zdim
    basis = [tuple(int(j == i) for j in range(ambient)) for i in range(ambient)]
    images = [acts_by_radical(node, e) for node in nodes for e in basis[:1+n]]
    nimages = rank(images, ambient)
    for line in basis[1+n:]:
        if rank(images+[line], ambient) <= nimages:
            continue
        assert all(acts_by_radical(node, line) == (0,)*ambient for node in nodes)
        return
    raise AssertionError("No line outside the image span.")


def small_exhaustion():
    n = 2
    zdim = n*(n+1)//2
    nodes = [(a[:n], a[n:]) for a in product(range(3),repeat=n+zdim)]
    tested = 0
    for x,z in nodes:
        expz = vadd(z, tuple((2*v) % 3 for v in symprod(x,x)))
        logz = vadd(expz, symprod(x,x))
        assert logz == z
        for y,w in nodes:
            expw = vadd(w, tuple((2*v) % 3 for v in symprod(y,y)))
            addxy = vadd(x,y)
            addzw = vadd(z,w)
            assert vadd(vadd(expz, expw), symprod(x,y)) == vadd(
                addzw, tuple((2*v) % 3 for v in symprod(addxy,addxy))
            )
            tested += 1
        nonzero_line(n, [(x,z)])
    return tested,len(nodes)


def bigger_profiles():
    n = 6
    zdim = n*(n+1)//2
    rng = Random(234)
    count = 0
    for k in range(1,n):
        for _ in range(14):
            nodes = [(tuple(rng.randrange(3) for _ in range(n)),
                      tuple(rng.randrange(3) for _ in range(zdim))) for _ in range(k)]
            nonzero_line(n, nodes)
            count += 1
    return count



def rmul(a,b,n):
    x,y=a[1:n+1],b[1:n+1]
    z,w=a[n+1:],b[n+1:]
    return ((a[0]*b[0])%3,) + tuple((a[0]*v+b[0]*u)%3 for u,v in zip(x,y)) + tuple(
        (a[0]*v+b[0]*u+t)%3 for u,v,t in zip(z,w,symprod(x,y))
    )


def rinverse(v,n):
    scalar=v[0]
    assert scalar in (1,2)
    one=(1,)+(0,)*(len(v)-1)
    scale=lambda c,x:tuple((c*w)%3 for w in x)
    e=vadd(scale(scalar,v),scale(-1,one))
    return scale(scalar,vadd(vadd(one,scale(-1,e)),rmul(e,e,n)))


def square_zero_profiles():
    rng=Random(220)
    normalized=rank_deficient=0
    for n in (2,6):
        d=1+n+n*(n+1)//2
        one=(1,)+(0,)*(d-1)
        zero=(0,)*d
        for k in range(1,n//2+2):
            for i in range(24):
                rows=[tuple(tuple(rng.randrange(3) for _ in range(d)) for _ in range(2))
                      for _ in range(k)]
                if i%3==0:
                    rows=[(a,(a[0],)+b[1:]) for a,b in rows]
                chosen=next(((j,l) for j in range(k) for l in range(j+1,k)
                             if (rows[j][0][0]*rows[l][1][0]-rows[j][1][0]*rows[l][0][0])%3),None)
                if chosen is None:
                    p,q=next((p,q) for p,q in product(range(3),repeat=2) if (p or q)
                             and all((p*a[0]+q*b[0])%3==0 for a,b in rows))
                    z=(0,)*(d-1)+(1,)
                    assert all(vadd(rmul(a,tuple(p*u%3 for u in z),n),
                                    rmul(b,tuple(q*u%3 for u in z),n))==zero for a,b in rows)
                    rank_deficient+=1
                    continue
                j,l=chosen
                a,b=rows[j]
                c,e=rows[l]
                neg=lambda t:tuple((-u)%3 for u in t)
                det=rinverse(vadd(rmul(a,e,n),neg(rmul(b,c,n))),n)
                inv=[(rmul(det,e,n),rmul(det,neg(c),n)),
                     (rmul(det,neg(b),n),rmul(det,a,n))]
                changed=[tuple(vadd(rmul(x,col[0],n),rmul(y,col[1],n)) for col in inv)
                         for x,y in rows]
                assert changed[j]==(one,zero) and changed[l]==(zero,one)
                nil=[(v[1:n+1],v[n+1:]) for i,row in enumerate(changed)
                      if i not in (j,l) for v in row]
                assert len(nil)<n
                nonzero_line(n,nil)
                normalized+=1
    return normalized,rank_deficient


if __name__ == "__main__":
    pairs, one = small_exhaustion()
    normalized, deficient = square_zero_profiles()
    print(json.dumps({
        "square_zero_normalized_rank_two_cases": normalized,
        "square_zero_common_kernel_cases": deficient,
        "exponential_product_pairs": pairs,
        "one_element_odd_centralizer_cases": one,
        "randomized_six_generator_space_tuple_cases": bigger_profiles()
    }, indent=2))
