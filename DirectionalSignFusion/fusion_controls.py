"""Exhaustive checks of the finite sign models and two small centroid bases."""

from itertools import combinations, product
import json

G = tuple(range(8))
E = 1
V = 6
D = 7


def directions(profile):
    return (E in profile) and (0 not in profile)


def profile_control():
    subspaces = []
    for n in (1, 2, 4, 8):
        for group in combinations(G, n):
            base = frozenset(group)
            if 0 in base and all(x ^ y in base for x in base for y in base):
                subspaces.append(base)
    profiles = sorted({tuple(sorted(x ^ a for x in s)) for s in subspaces for a in G},
                      key=lambda s: (len(s), s))
    assert len(profiles) == 51
    for a, b in product((False, True), repeat=2):
        pa = (0, D) if a else (0,)
        pb = (0, V) if b else (0,)
        assert directions({V ^ x ^ y for x in pa for y in pb}) == (a and not b)
    bits = (1 << len(profiles)) - 1
    target = sum((0 in s) << i for i, s in enumerate(profiles))
    witnessed = sum((E in s) << i for i, s in enumerate(profiles))
    patterns = set()
    for c, u, v, w in product(G, repeat=4):
        image = [c ^ (u if x & 1 else 0) ^ (v if x & 2 else 0) ^ (w if x & 4 else 0) for x in G]
        out = sum(directions({image[x] for x in p}) << i for i, p in enumerate(profiles))
        patterns.add(out)
    assert target not in patterns and (bits ^ target) not in patterns
    for rail in (target, bits ^ target):
        assert all((x & y) != rail and (x | y) != rail for x in patterns for y in patterns)
    cross = {p & witnessed for p in patterns}
    yes_witnessed = witnessed & target
    assert yes_witnessed not in cross and (witnessed ^ yes_witnessed) in cross
    return {"profiles": len(profiles), "affine_queries": 8**4,
            "distinct_query_truth_tables": len(patterns),
            "difference_switch_cases": 4, "witnessed_profiles": witnessed.bit_count()}


def centroid_test(n):
    # R = F_3[t]/t^n. The pencil on the right has multipliers 0, 1, -1.
    left, right = 2*n, 3*n
    first_size = left*left
    second_size = right*right
    variables = first_size + 2*second_size
    rows = {}

    def component(a, b):
        power = a % n + b % n
        coefficient = 1 if a < n else (0, 1, 2)[b // n]
        if not coefficient or power >= n:
            return -1, 0
        return n*(b // n)+power, coefficient

    def add(row):
        row = {k: v % 3 for k, v in row.items() if v % 3}
        while row:
            key = min(row)
            value = row[key]
            if key not in rows:
                rows[key] = {i: (value*v) % 3 for i, v in row.items()}
                return
            for i, v in rows[key].items():
                change = (row.get(i, 0) - value*v) % 3
                if change:
                    row[i] = change
                else:
                    row.pop(i, None)

    for i in range(left):
        for j in range(right):
            z, factor = component(i, j)
            for k in range(right):
                xrow, yrow = {}, {}
                if factor:
                    p = first_size + second_size + k*right + z
                    xrow[p] = yrow[p] = -factor
                for s in range(left):
                    out, mul = component(s, j)
                    if out == k:
                        xrow[s*left+i] = mul
                for t in range(right):
                    out, mul = component(i, t)
                    if out == k:
                        yrow[first_size+t*right+j] = mul
                add(xrow)
                add(yrow)
    nullity = variables - len(rows)
    assert nullity == n
    return nullity


def ring_unit_control():
    checks = 0
    for p in (2, 3, 5, 7, 11, 13, 17, 19):
        for ratio in range(1, p):
            ratio_powers = {pow(ratio, i, p) for i in range(p-1)}
            for sign in (1, p-1):
                for power in ratio_powers:
                    data, keep_pin, relax_pin = sign*power % p, sign*power % p, sign
                    if keep_pin == 1:
                        assert data == 1
                    if relax_pin == 1:
                        assert data in ratio_powers
                    checks += 1
            assert ratio in ratio_powers
    return checks


if __name__ == "__main__":
    out = profile_control()
    out["pencil_centroid_dimensions"] = {str(n): centroid_test(n) for n in (1, 2, 4)}
    out["localization_unit_screen_cases"] = ring_unit_control()
    print(json.dumps(out, indent=2))
