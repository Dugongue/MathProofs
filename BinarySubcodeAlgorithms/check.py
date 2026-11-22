"""Exact controls for the tree, spectrum rules and random-supercode formula."""
from fractions import Fraction
from itertools import combinations, permutations
from math import comb, factorial, prod
from random import Random

from subcode import (basis, count_embeddings, count_group_epimorphisms, dual, prune_target, positions,
                     quotient_spectrum, reduce_word, tighten, weight_classes, words)


def all_codes(r):
    known = {()}
    frontier = [()]
    while frontier:
        rows = frontier.pop()
        for v in range(1, 1 << r):
            new = basis((*rows, v))
            if new not in known:
                known.add(new)
                frontier.append(new)
    return sorted(known)


def permute(v, p):
    return sum(1 << p[i] for i in positions(v))


def check_pair(r, c, d, perms):
    valid = {p for p in perms if all(reduce_word(permute(v,p), d)==0 for v in c)}
    a, b = tighten(r,c,d)
    assert valid == {p for p in perms if all(reduce_word(permute(v,p), b)==0 for v in a)}
    for prune in (False, True):
        n, p, _ = count_embeddings(r,c,d,prune=prune)
        assert n == len(valid)
        assert (p in valid) if n else (p is None)


def gaussian(n, k):
    if not 0 <= k <= n:
        return 0
    return prod(2**n-2**i for i in range(k)) // prod(2**k-2**i for i in range(k))


def check_forbidden(r, codes):
    tests = 0
    for c in codes:
        for w in range(1,r+1):
            if weight_classes(c).get(w,()) != c:
                continue
            f = {reduce_word(v,c) for v in range(1 << r) if v.bit_count()==w} - {0}
            assert len(f) == quotient_spectrum(r,c,{w})
            N = r-len(c)
            all_super = [d for d in codes if all(reduce_word(x,d)==0 for x in c)]
            for g in range(N+1):
                hosts = [d for d in all_super if len(d)==len(c)+g]
                counts = [0]*(g+1)
                for d in hosts:
                    available = weight_classes(d).get(w, ())
                    t = len(available)-len(c)
                    assert t == len(basis(x for x in f if not reduce_word(x,d)))
                    counts[t] += 1
                exact = 0
                for sz in range(len(f)+1):
                    for subset in combinations(f,sz):
                        rank = len(basis(subset))
                        exact += (-1)**sz * gaussian(N-rank, g-rank)
                assert counts[0] == exact and len(hosts)==gaussian(N,g)
                for j in range(1,g+1):
                    bound = (comb(len(f),j) if j <= len(f) else 0) * prod(
                        Fraction(2**g-2**i,2**N-2**i) for i in range(j))
                    assert Fraction(sum(counts[j:]),len(hosts)) <= bound
                tests += 1
    return tests


if __name__ == "__main__":
    for m in (1,2,3):
        r = 4*m
        c = [3 << (2*i) for i in range(2*m)]
        for size in (2*m,2*m-1):
            e = (1 << size)-1
            d = dual(r,(e, ((1 << r)-1)^e))
            n, p = count_group_epimorphisms(r,c,d)
            expected = comb(2*m,m)*factorial(2*m)**2 if size==2*m else 0
            assert n == expected * 6**r * 2**(2*r)
            assert (p is None) == (expected == 0)
    c = basis((141,74,37,27))
    d = basis((*c, 7 << 8, 31 << 11))
    assert prune_target(16,c,d) == c
    cw, dw = weight_classes(c), weight_classes(d)
    for sz in range(len(cw)+1):
        for mask in combinations(cw,sz):
            if basis(v for w in mask for v in cw[w]) == c:
                assert len(basis(v for w in mask for v in dw[w])) > len(c)
    pairs = spectra = 0
    for r in range(5):
        codes = all_codes(r)
        perms = list(permutations(range(r)))
        for c in codes:
            assert dual(r,dual(r,c)) == c
            for d in codes:
                check_pair(r,c,d,perms)
                pairs += 1
        spectra += check_forbidden(r,codes)
    rng = Random(314159)
    extra = 0
    for r in (5,6,7):
        perms = list(permutations(range(r)))
        for _ in range(7):
            c = basis(rng.randrange(1 << r) for _ in range(rng.randrange(r+1)))
            d = basis(rng.randrange(1 << r) for _ in range(rng.randrange(r+1)))
            check_pair(r,c,d,perms)
            extra += 1
    print(f"{pairs} ordered pairs through length 4 and {extra} longer pairs agree "
          f"on counts and witnesses. All {spectra} quotient-spectrum tests passed.")
