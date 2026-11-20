"""Finite replay of the class-two query construction's algebraic ingredients."""

from itertools import combinations, product
from math import gcd, prod
from random import Random
import json


def vectors(orders):
    return product(*(range(n) for n in orders))


def scale(a, v, orders):
    return tuple(a * x % n for x, n in zip(v, orders))


def add(v, w, orders):
    return tuple((x + y) % n for x, y, n in zip(v, w, orders))


def span(gs, orders):
    result = {(0,) * len(orders)}
    for g in gs:
        cyc = {scale(a, g, orders) for a in range(max(orders))}
        result = {add(v, w, orders) for v in result for w in cyc}
    return frozenset(result)


def image(matrix, orders, modulus):
    return {
        tuple(sum(x * a for x, a in zip(v, row)) % modulus for row in matrix)
        for v in vectors(orders)
    }


def check_pairs(rng):
    intersections = 0
    for p, e in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2)):
        modulus = p**e
        for trial in range(22):
            x = (p**rng.randint(1, e),)
            if e <= 2 and trial % 3 == 0:
                x += (p,)
            w = (p, p**rng.randint(1, e))
            orders = x + x + w
            n, size = len(x), len(orders)
            q = [[0] * size for _ in range(size)]
            for i, j in combinations((*range(n), *range(2*n, size)), 2):
                d = gcd(orders[i], orders[j])
                v = rng.randrange(d) * (modulus // d)
                if trial % 2 == 0 and i >= 2*n:
                    v = 0
                q[i][j], q[j][i] = v, -v
            u = rng.choice([a for a in range(modulus) if a % p])
            for i, o in enumerate(x):
                v = u * (modulus // o)
                q[i][n+i], q[n+i][i] = v, -v
            result = image(q, orders, modulus)
            residual = image([row[2*n:] for row in q[2*n:]], w, modulus)
            assert len(result) == prod(x)**2 * len(residual)
            for a in range(modulus):
                # A private rank-two heavy block adds this factor.
                heavy = (modulus // gcd(modulus, a))**2
                assert (len(result)*heavy == prod(x)**2) == (a == 0 and len(residual) == 1)
            if len(residual) == 1:
                seen = {v[:n] for v in result if not any(v[n:])}
                wanted = {tuple(a * (modulus // o) for a, o in zip(v, x))
                          for v in vectors(x)}
                assert seen == wanted
                intersections += 1
    return 110, intersections


def check_bands():
    count = 0
    for r in (2, 4, 7, 18):
        d = 3*r
        weights = [2*(9+i)*(d+1) for i in range(8)]
        for states in product((0, 1, 2), repeat=8):
            # 0 is zero, 1 is nonzero nonunit, 2 is a unit.
            units = [i for i, state in enumerate(states) if state == 2]
            for residual in (0, d//2, d):
                rank = sum(weights[i] for i in units) + residual
                observed = [i for i, w in enumerate(weights) if w <= rank <= w+d]
                assert observed == (units if len(units) == 1 else [])
                count += 1
    return count


def slots(n):
    if n <= 6:
        return [(i,) for i in range(n) for _ in range(i+1)] + [(n,)]*(n+1)
    edges = [(0, 1), (0, 2), (2, 3), (0, 4)] + [(i-1, i) for i in range(5, n)]
    return [(i,) for i in range(n)] + [(n,)]*2 + edges


def check_frames(rng):
    contractions = incidence = 0
    for p, e in ((2, 1), (2, 2), (2, 3), (3, 2)):
        for n in (2, 4, 6, 7, 8):
            orders = (p**e, p**e) + tuple(p**rng.randint(1, e) for _ in range(n-2))
            basis = [tuple(int(i == j) for j in range(n)) for i in range(n)] + [(1,)*n]
            pieces = [[basis[i] for i in ix] for ix in slots(n)]
            lengths = [max((orders + (p**e,))[i] for i in ix) for ix in slots(n)]
            expected = {span([g], orders) for g in basis}
            cyclic = set()
            cases = [{j: a} for j, d in enumerate(lengths) for a in range(d)]
            for _ in range(20):
                js = rng.sample(range(len(pieces)), 2)
                cases.append({j: rng.randrange(lengths[j]) for j in js})
            for coeffs in cases:
                result = span([scale(a, g, orders) for j, a in coeffs.items() for g in pieces[j]], orders)
                if 1 < len(result) <= p**e and any(span([g], orders) == result for g in result):
                    cyclic.add(result)
                contractions += 1
            assert {line for line in cyclic if not any(line < y for y in cyclic)} == expected
            blocks = list(expected) + [span([basis[i], basis[j]], orders)
                                       for i, j in combinations(range(n), 2)]
            for block in blocks:
                observed = 0
                for generators, d in zip(pieces, lengths):
                    mod_p = {a % p for a in range(d)
                             if all(scale(a, g, orders) in block for g in generators)}
                    observed += len(mod_p) > 1
                assert observed == sum(all(g in block for g in part) for part in pieces)
                incidence += 1
    return contractions, incidence


def check_powers():
    cases = anchors = 0
    for p, e in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2)):
        m = p**e
        orders = (m, p, m, m, p)
        center = (p, m, p)
        zero = (0,)*5
        for first, second in ((0, 0), (1, 0), (1, 1)):
            def power(v, d):
                x, z = zero, (0, 0, 0)
                for _ in range(d):
                    a, b, u, _, _ = ((xx + vv)//o for xx, vv, o in zip(x, v, orders))
                    correction = (a*first+b*second-x[1]*v[0], u-x[3]*v[2], x[4]*v[2])
                    x, z = add(x, v, orders), add(z, correction, center)
                return x, z

            for d in (p**a for a in range(1, e+1)):
                for v in vectors(orders):
                    if scale(d, v, orders) != zero:
                        continue
                    x, z = power(v, d)
                    y, w = power(v[:-1] + (0,), d)
                    assert x == y == zero and z[:2] == w[:2]
                    cases += 1
            for u in range(1, m):
                if u % p:
                    z = power((0, 0, u, 0, 0), m)[1][1]
                    assert z == u and ((u*u-z) % m == 0) == (u == 1)
                    anchors += 1
    return cases, anchors


def main():
    pairs, intersections = check_pairs(Random(20261120))
    contractions, incidence = check_frames(Random(20261121))
    powers, anchors = check_powers()
    print(json.dumps({
        "paired_image_cardinalities": pairs,
        "zero_residual_intersections": intersections,
        "rank_band_cases": check_bands(),
        "frame_contractions": contractions,
        "frame_incidence_cases": incidence,
        "power_record_cases": powers,
        "unit_power_pins": anchors,
    }, indent=2))


if __name__ == "__main__":
    main()
