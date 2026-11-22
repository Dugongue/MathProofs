"""Check extremal marks from explicit subspaces and from Legendre symbols."""
from itertools import combinations, product
from math import prod
import json


def add_span(space, v, p):
    return frozenset(tuple((x + i*y) % p for x, y in zip(u, v))
                     for u in space for i in range(p))


def check(p, r):
    vectors = list(product(range(p), repeat=r))
    spaces = {frozenset({(0,)*r}): 0}
    frontier = list(spaces)
    for space in frontier:
        for v in vectors:
            if v not in space:
                bigger = add_span(space, v, p)
                if bigger not in spaces:
                    spaces[bigger] = spaces[space] + 1
                    frontier.append(bigger)
    weights = {}
    for space, dim in spaces.items():
        codim = r - dim
        numerator = p * (-1)**codim * p**(codim*(codim-1)//2)
        assert numerator % (p**codim) == 0
        weights[space] = numerator
    for sub, dim in spaces.items():
        assert sum(value for space, value in weights.items() if sub <= space) == (p if dim == r else 0)
    degree = sum(w for w in weights.values() if w > 0)
    assert degree == -sum(w for w in weights.values() if w < 0)
    assert 2*degree == p * prod(1+p**i for i in range(r))
    return dict(prime=p, rank=r, subgroups=len(spaces), degree=degree)


def prime_example():
    primes = [p for p in range(7,100) if all(p%d for d in range(2,int(p**0.5)+1))]
    def frob(p):
        return tuple(int(pow(a,(p-1)//2,p) != 1) for a in (2,3,5))
    def counts(prime_tuple):
        space = frozenset({(0,0,0)})
        for p in prime_tuple:
            space = add_span(space,frob(p),2)
        vectors = list(product(range(2),repeat=3))[1:]
        return (2+4*sum(space <= {(0,0,0),v} for v in vectors),
                2*8*int(len(space)==1)+2*sum(all(sum(i*j for i,j in zip(x,v))%2==0
                    for x in space) for v in vectors))
    for j in range(3):
        for ps in combinations(primes,j):
            a,b=counts(ps)
            assert a==b
    first=next(ps for ps in combinations(primes,3) if counts(ps)[0]!=counts(ps)[1])
    return dict(radicands=[2,3,5],tested_primes=primes,distinguishing_primes=first,counts=counts(first))


if __name__ == "__main__":
    print(json.dumps(dict(lattices=[check(p,r) for p,r in [(2,1),(2,2),(2,3),(2,4),(3,2),(3,3)]],
                         triquadratic=prime_example()),indent=2))
