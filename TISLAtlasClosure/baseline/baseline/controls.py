"""Finite controls for the linear-switch and cross-characteristic arguments."""

from itertools import permutations, product
import json
from random import Random


def subgroups_mod(m):
    return [frozenset(range(0, m, d))
            for d in range(1, m+1) if m % d == 0]


def shift_controls():
    checks = 0
    for m in range(2, 8):
        for p in permutations(range(m)):
            is_shift = all(p[(x+1) % m] == (p[x]+1) % m for x in range(m))
            if not is_shift:
                continue
            z = p[0]
            assert p == tuple((x+z) % m for x in range(m))
            for distinct in (False, True):
                labels = (int(distinct),) + (0,)*(m-1)
                assert all(labels[p[x]] == labels[x] for x in range(m)) == (not distinct or z == 0)
                checks += 1
        for a, b, c in product(range(m), repeat=3):
            assert all((x+y+c) % m == (x+a+y+b) % m for x, y in product(range(m), repeat=2)) == (c == (a+b) % m)
            checks += 1
    return checks


def affine_controls():
    checks = 0
    for m in range(2, 6):
        for h in subgroups_mod(m):
            for c in range(m):
                values = sorted({(c+x) % m for x in h})
                encoded = set()
                for weights in product(range(m), repeat=len(values)):
                    if sum(weights) % m == 1:
                        encoded.add(sum(w*v for w, v in zip(weights, values)) % m)
                    checks += 1
                assert encoded == set(values)
    for x in range(8):
        for y in range(8):
            for z in range(8):
                space = {0,x,y,z,x^y,x^z,y^z,x^y^z}
                cols = sorted(space)
                for c in range(8):
                    values = [c ^ h for h in cols]
                    encoded = set()
                    for mask in range(1 << len(values)):
                        if mask.bit_count() % 2 == 0:
                            continue
                        value = 0
                        for i, v in enumerate(values):
                            if mask & (1 << i):
                                value ^= v
                        encoded.add(value)
                        checks += 1
                    assert encoded == set(values)
    return checks


def arbitrary_rank_controls():
    rng = Random(267)
    checks = 0
    for _ in range(320):
        # Random affine profiles in F2^2, coupled across 3 blocks.
        profiles = []
        for _ in range(3):
            d, a, b = [rng.randrange(4) for _ in range(3)]
            profiles.append(sorted({d, d^a, d^b, d^a^b}) if rng.randrange(10) else [])
        dimension = rng.randrange(1, 13)
        coefficients = [(rng.randrange(1 << dimension), rng.randrange(1 << dimension))
                        for _ in profiles]

        def image(i, v):
            a, b = coefficients[i]
            return (a if v & 1 else 0) ^ (b if v & 2 else 0)

        direct = {image(0, a) ^ image(1, b) ^ image(2, c)
                  for a, b, c in product(*profiles)}
        slots = [(i, image(i, v)) for i, values in enumerate(profiles) for v in values]
        reachable = {0}
        for i, value in slots:
            column = (value << 3) ^ (1 << i)
            reachable |= {old ^ column for old in reachable}
        encoded = {x >> 3 for x in reachable if x & 7 == 7}
        assert encoded == direct
        checks += 1
    assert not (0 in {1, 2, 3}) and 1 ^ 2 ^ 3 == 0
    return checks


def shear_controls():
    sizes = []
    for q in (2, 3, 5):
        vectors = list(product(range(q), repeat=3))
        orbit = {(1, 0, 0)}
        todo = list(orbit)
        while todo:
            v = todo.pop()
            for i in range(3):
                for j in range(3):
                    if i == j:
                        continue
                    for a in range(1, q):
                        w = list(v)
                        w[i] = (w[i]+a*w[j]) % q
                        w = tuple(w)
                        if w not in orbit:
                            orbit.add(w)
                            todo.append(w)
        assert set(vectors) - {(0,0,0)} == orbit
        sizes.append(len(orbit))
    return sizes


if __name__ == "__main__":
    print(json.dumps({
        "cyclic_switch_and_sum_cases": shift_controls(),
        "affine_weight_cases": affine_controls(),
        "coupled_systems": arbitrary_rank_controls(),
        "nonzero_character_orbit_sizes": shear_controls(),
    }, indent=2))
