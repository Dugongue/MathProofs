"""Finite controls for hidden marker recovery."""

from itertools import permutations
from math import comb
from random import Random


def trim(f):
    while f and f[-1] == 0:
        f.pop()
    return f


def mul(f, g, p):
    if not f or not g:
        return []
    answer = [0] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            answer[i + j] = (answer[i + j] + x * y) % p
    return trim(answer)


def divmod_poly(f, g, p):
    f = f.copy()
    q = [0] * max(0, len(f) - len(g) + 1)
    inv = pow(g[-1], -1, p)
    while len(f) >= len(g):
        i = len(f) - len(g)
        q[i] = f[-1] * inv % p
        for j, y in enumerate(g):
            f[i + j] = (f[i + j] - q[i] * y) % p
        trim(f)
    return trim(q), f


def divide(f, g, p):
    quotient, remainder = divmod_poly(f, g, p)
    assert not remainder
    return quotient


def gcd_poly(f, g, p):
    while g:
        f, g = g, divmod_poly(f, g, p)[1]
    return [x * pow(f[-1], -1, p) % p for x in f]


def power(f, n, p):
    answer = [1]
    for _ in range(n):
        answer = mul(answer, f, p)
    return answer


def hasse(f, j, p):
    return trim([comb(i, j) * f[i] % p for i in range(j, len(f))])


def squarefree_support(f, p):
    if len(f) == 1:
        return [1]
    derivative = hasse(f, 1, p)
    if not derivative:
        assert all(i % p == 0 for i, v in enumerate(f) if v)
        return squarefree_support(f[::p], p)
    g = gcd_poly(f, derivative, p)
    a = divide(f, g, p)
    b = squarefree_support(g, p)
    return divide(mul(a, b, p), gcd_poly(a, b, p), p)


def labeled_recovery(p):
    weights = (22, 42, 82)
    factors = [[-a % p, 1] for a in (0, 1, 2)]
    f = [1]
    for g, power_count in zip(factors, weights):
        f = mul(f, power(g, power_count, p), p)
    supports = []
    for cutoff in weights:
        g = f
        for j in range(1, cutoff):
            g = gcd_poly(g, hasse(f, j, p), p)
        supports.append(squarefree_support(g, p))
    got = [divide(a, b, p) for a, b in zip(supports, supports[1:] + [[1]])]
    assert got == factors
    print(f"F_{p}: recovered labeled roots with exponents {weights}")


def rank(rows, p):
    pivots = {}
    for row in rows:
        vector = {i: x for i, x in enumerate(row) if x % p}
        while vector:
            at = min(vector)
            entry = vector[at]
            if at not in pivots:
                inverse = pow(entry, -1, p)
                pivots[at] = {i: x * inverse % p for i, x in vector.items()}
                break
            for i, x in pivots[at].items():
                value = (vector.get(i, 0) - entry * x) % p
                if value:
                    vector[i] = value
                else:
                    vector.pop(i, None)
    return len(pivots)


def build_marked():
    triples = [(0, 2, 4)]
    marker_indices = (146, 147, 148)
    aux_start = 6
    for role, (size, marker) in enumerate(zip((20, 40, 80), marker_indices)):
        triples.append((2 * role, 2 * role + 1, marker))
        triples.extend((i, i + 1, marker) for i in range(aux_start, aux_start + size, 2))
        aux_start += size
    assert aux_start == marker_indices[0]
    return tuple(ordered for triple in triples for ordered in permutations(triple))


def rank_drop_control(p, seed):
    n = 149
    triples = build_marked()
    rng = Random(seed)
    checks = 0
    for omitted in (-1, 0, 1, 2):
        for _ in range(3):
            x = [rng.randrange(p) for _ in range(n - 3)] + [1] * 3
            if omitted != -1:
                x[n - 3 + omitted] = 0
            m = [[0] * n for _ in range(n)]
            for a, b, c in triples:
                m[b][c] = (m[b][c] + x[a]) % p
            # Hide the rows and columns by simultaneous elementary changes.
            for _ in range(22):
                i, j = rng.sample(range(n), 2)
                a = rng.randrange(1, p)
                m[i] = [(u + a * v) % p for u, v in zip(m[i], m[j])]
                for row in m:
                    row[i] = (row[i] + a * row[j]) % p
            actual = rank(m, p)
            assert (actual < n - 9) == (omitted != -1)
            checks += 1
    print(f"F_{p}: {checks} direct rank-gap tests on hidden slice matrices of dimension {n}")


def splitting_control():
    # Three determinant components, including an irreducible spurious component in F_2.
    p = 2
    at_zero, at_one, irreducible = [0, 1], [1, 1], [1, 1, 1]
    diagonal = [at_zero] * 4 + [at_one] * 3 + [irreducible] + [[1]] * 2
    determinant = [1]
    for entry in diagonal:
        determinant = mul(determinant, entry, p)
    branches = [(determinant, 0)]
    for pivot in diagonal:
        next_branches = []
        for f, prior_rank in branches:
            g = gcd_poly(f, pivot, p)
            saturated = gcd_poly(f, power(g, len(f) - 1, p), p)
            complement = divide(f, saturated, p)
            if len(saturated) > 1:
                next_branches.append((saturated, prior_rank))
            if len(complement) > 1:
                next_branches.append((complement, prior_rank + 1))
        branches = next_branches
    selected = [1]
    for modulus, actual_rank in branches:
        if actual_rank < 8:
            selected = mul(selected, modulus, p)
    assert sorted(r for _, r in branches) == [6, 7, 9]
    assert squarefree_support(selected, p) == mul(at_zero, at_one, p)
    print("F_2: gcd rank splitting retained both linear markers and excluded a spurious irreducible")


if __name__ == "__main__":
    for prime in (2, 3, 5):
        rank_drop_control(prime, 164 + prime)
    for prime in (3, 5, 7):
        labeled_recovery(prime)
    splitting_control()
