"""Exact small-prime replay of the separable IPS synthesis theorem."""

from itertools import product
from random import Random


def add(a, b, p):
    result = [0] * max(len(a), len(b))
    for poly in (a, b):
        for i, c in enumerate(poly):
            result[i] = (result[i] + c) % p
    while result and result[-1] == 0:
        result.pop()
    return result


def scale(a, c, p):
    return add([], [(c * x) % p for x in a], p)


def mul(a, b, p):
    result = [0] * max(0, len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] = (result[i + j] + x * y) % p
    return add([], result, p)


def evaluate(poly, a, p):
    result = 0
    for x in reversed(poly):
        result = (result * a + x) % p
    return result


def quotient(a, monic, p):
    rest = list(a)
    result = [0] * max(0, len(a) - len(monic) + 1)
    while len(rest) >= len(monic):
        offset = len(rest) - len(monic)
        result[offset] = rest[-1]
        rest = add(rest, [0] * offset + scale(monic, -result[offset], p), p)
    return result


def grid_data(points, p):
    basis = {}
    for a in points:
        poly = [1]
        for b in points:
            if b != a:
                poly = mul(poly, [-b, 1], p)
        basis[a] = scale(poly, pow(evaluate(poly, a, p), -1, p), p)
    assert all(evaluate(poly, b, p) == (a == b)
               for a, poly in basis.items() for b in points)
    monic = [1]
    for a in points:
        monic = mul(monic, [-a, 1], p)
    return basis, monic


def scan_capped(values, cap, p):
    states = [{0: ()}]
    for v in values:
        if states[-1] is None:
            states.append(None)
            continue
        next_set = {}
        overflow = False
        for s, witness in states[-1].items():
            for a, y in v.items():
                next_set.setdefault((s + y) % p, witness + (a,))
                if len(next_set) == cap + 1:
                    overflow = True
                    break
            if overflow:
                break
        states.append(None if overflow else next_set)
    return states


def synthesize(points, us, b, p):
    n = len(points)
    values = [{a: evaluate(u, a, p) for a in grid}
              for grid, u in zip(points, us)]
    cap = 1
    while True:
        pref = scan_capped(values, cap, p)
        suff = scan_capped(reversed(values), cap, p)[::-1]
        counts = [min(cap + 1 if a is None else len(a), cap + 1 if b is None else len(b))
                  for a, b in zip(pref, suff)]
        r = max(counts)
        if r <= cap:
            break
        cap *= 2
    pivot = next((k - 1 for k in range(1, n + 1)
                  if pref[k] is None or len(pref[k]) > r), n - 1)
    assert pref[pivot] is not None and suff[pivot + 1] is not None
    for s, left in pref[pivot].items():
        for t, right_reversed in suff[pivot + 1].items():
            for a, value in values[pivot].items():
                if (b + s + value + t) % p == 0:
                    return r, left + (a,) + right_reversed[::-1], None
    state_sets = [list(pref[k]) if k <= pivot else list(suff[k])
                  for k in range(n + 1)]
    dimensions = list(map(len, state_sets))
    assert max(dimensions) <= r
    ordinary_layers = []
    certificate_layers = []
    for k in range(n):
        lagrange, monic = grid_data(points[k], p)
        ordinary = []
        marked_x = []
        for i, prefix in enumerate(state_sets[k]):
            for j, suffix in enumerate(state_sets[k + 1]):
                entry = []
                for a, v in values[k].items():
                    if k < pivot:
                        factor = int((prefix + v) % p == suffix)
                    elif k > pivot:
                        factor = int(prefix == (suffix + v) % p)
                    else:
                        factor = pow((b + prefix + v + suffix) % p, -1, p)
                    entry = add(entry, scale(lagrange[a], factor, p), p)
                if entry:
                    ordinary.append((i, j, entry))
                    marked_x.extend([(i, j, entry),
                                     (dimensions[k] + i, 2 * dimensions[k + 1] + j, entry)])
                    q = quotient(mul(us[k], entry, p), monic, p)
                    if any(q):
                        marked_x.append((i, dimensions[k + 1] + j, q))
        marked_z = []
        for j in range(dimensions[k + 1]):
            d = dimensions[k + 1]
            marked_z.extend([(j, j, [1]), (d + j, d + j, [0, 1]),
                             (2 * d + j, d + j, [1])])
        ordinary_layers.append(ordinary)
        certificate_layers.extend([marked_x, marked_z])
    certificate_layers.append([(0, 0, [0, 1]), (1, 0, [-1])])
    return r, None, (ordinary_layers, certificate_layers)


def increment(polynomial, key, value, p):
    coeff = (polynomial.get(key, 0) + value) % p
    if coeff:
        polynomial[key] = coeff
    elif key in polynomial:
        del polynomial[key]


def expand(layers, p):
    states = {0: {(0,) * len(layers): 1}}
    for i, layer in enumerate(layers):
        after = {}
        for u, v, label in layer:
            if u in states:
                target = after.setdefault(v, {})
                for exponents, a in states[u].items():
                    for k, b in enumerate(label):
                        if b:
                            key = exponents[:i] + (exponents[i] + k,) + exponents[i + 1:]
                            increment(target, key, a * b, p)
        states = after
    return states.get(0, {})


def flatten(poly, cut):
    left = sorted({exponents[:cut] for exponents in poly})
    right = sorted({exponents[cut:] for exponents in poly})
    return [[poly.get(a + b, 0) for b in right] for a in left]


def rank(matrix, p):
    rows = [list(row) for row in matrix]
    if not rows:
        return 0
    pivot = 0
    for j in range(len(rows[0])):
        k = next((i for i in range(pivot, len(rows)) if rows[i][j]), None)
        if k is None:
            continue
        rows[pivot], rows[k] = rows[k], rows[pivot]
        a = rows[pivot]
        inv = pow(a[j], -1, p)
        for row in rows[pivot + 1:]:
            if row[j]:
                scale = row[j] * inv
                for col in range(j, len(row)):
                    row[col] = (row[col] - scale * a[col]) % p
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def substitute(certificate, points, us, b, p):
    n = len(points)
    result = {}
    monics = [grid_data(grid, p)[1] for grid in points]
    for powers, c in certificate.items():
        x = powers[0:2 * n:2]
        markers = [powers[2 * i + 1] for i in range(n)]
        y = powers[-1]
        assert y + sum(markers) == 1 and max(markers + [y]) == 1
        assert all(e < len(grid) for e, grid in zip(x, points))
        if y:
            increment(result, x, c * b, p)
            substitutions = enumerate(us)
        else:
            i = markers.index(1)
            substitutions = [(i, monics[i])]
        for i, polynomial in substitutions:
            for j, scalar in enumerate(polynomial):
                exponent = x[:i] + (x[i] + j,) + x[i + 1:]
                increment(result, exponent, c * scalar, p)
    return result


def eval_sparse(poly, point, p):
    value = 0
    for alpha, c in poly.items():
        term = c
        for a, e in zip(point, alpha):
            term = (term * pow(a, e, p)) % p
        value = (value + term) % p
    return value


def check_instance(points, us, b, p):
    n = len(points)
    vr = [[evaluate(u, a, p) for a in grid] for grid, u in zip(points, us)]
    left = [{sum(x) % p for x in product(*vr[:i])} for i in range(n + 1)]
    right = [{sum(x) % p for x in product(*vr[i:])} for i in range(n + 1)]
    cuts = [min(len(a), len(b)) for a, b in zip(left, right)]
    r, witness, rep = synthesize(points, us, b, p)
    assert r == max(cuts)
    evaluations = [(point, (b + sum(evaluate(u, a, p) for a, u in zip(point, us))) % p)
                   for point in product(*points)]
    if witness is not None:
        assert any(witness == x and v == 0 for x, v in evaluations)
        return False, r, None
    assert all(v != 0 for _, v in evaluations)
    ordinary, marked = rep
    reciprocal = expand(ordinary, p)
    certificate = expand(marked, p)
    assert all(eval_sparse(reciprocal, point, p) * v % p == 1
               for point, v in evaluations)
    assert substitute(certificate, points, us, b, p) == {(0,) * n: 1}
    assert all(rank(flatten(reciprocal, i), p) == w for i, w in enumerate(cuts))
    ranks = [rank(flatten(certificate, i), p) for i in range(2 * n + 2)]
    assert max(ranks) <= 3 * r
    if all(tuple(g) == (0, 1) and len(u) == 2 and u[0] == 0 for g, u in zip(points, us)):
        for i in range(n + 1):
            assert ranks[2 * i] == 2 * cuts[i] - int(len(right[i]) >= len(left[i]))
    return True, r, max(ranks)


def sumset(types, p, cap=None):
    sums = {0}
    for layer in types:
        sums = {(a + b) % p for a in sums for b in layer}
        if cap is not None and len(sums) > cap:
            return None
    return sums


def find_order(types, bound, p):
    for pivot in range(len(types)):
        remaining = [j for j in range(len(types)) if j != pivot]
        union = {a for j in remaining for a in types[j]} - {0}
        if len(union) > 2 * (bound - 1):
            continue
        by_type = {}
        zeros = []
        for j in remaining:
            if types[j] == (0,):
                zeros.append(j)
            else:
                by_type.setdefault(types[j], []).append(j)
        clipped = [min(len(indices), 2 * bound + 1) for indices in by_type.values()]
        for left_counts in product(*(range(c + 1) for c in clipped)):
            left = list(zeros)
            right = []
            for indices, clipped_count, left_count in zip(by_type.values(), clipped, left_counts):
                left.extend(indices[:left_count])
                right.extend(indices[left_count:clipped_count])
            if (sumset([types[j] for j in left], p, bound) is None
                    or sumset([types[j] for j in right], p, bound) is None):
                continue
            for indices, clipped_count, left_count in zip(by_type.values(), clipped, left_counts):
                if left_count >= bound:
                    side = left
                else:
                    assert clipped_count == len(indices) or clipped_count - left_count >= bound
                    side = right
                side.extend(indices[clipped_count:])
            assert sorted(left + [pivot] + right) == list(range(len(types)))
            assert sumset([types[j] for j in left], p, bound) is not None
            assert sumset([types[j] for j in right], p, bound) is not None
            return left + [pivot] + right
    return None


def independent_width(types, order, p):
    layers = [types[j] for j in order]
    return max(min(len(sumset(layers[:j], p)), len(sumset(layers[j:], p)))
               for j in range(len(layers) + 1))


def check_orders(rng):
    from itertools import permutations
    cases = 0
    for p in (2, 3, 5, 7):
        for _ in range(10):
            types = [tuple(sorted({0, *rng.sample(range(p), rng.randrange(1, p + 1))}))
                     for _ in range(rng.randrange(1, 7))]
            optimum = min(independent_width(types, order, p)
                          for order in permutations(range(len(types))))
            for bound in range(1, p + 1):
                result = find_order(types, bound, p)
                assert (result is not None) == (optimum <= bound)
                if result is not None:
                    assert independent_width(types, result, p) <= bound
                cases += 1
    for types, p, bound, expected in (
        ([(0, 1)] * 40, 2, 2, True),
        ([(0, 1), (0, 1, 2), (0, 2)] * 15, 3, 3, True),
        ([(0, 1)] * 90, 101, 3, False),
    ):
        result = find_order(types, bound, p)
        assert (result is not None) == expected
        if result is not None:
            assert independent_width(types, result, p) <= bound
        cases += 1
    return cases

def main():
    rng = Random(8312420)
    zeros = 0
    certificates = 0
    for p in (2, 3, 5, 7, 11):
        for _ in range(100):
            points = [sorted(rng.sample(range(p), rng.randrange(1, min(p, 4) + 1)))
                      for _ in range(rng.randrange(1, 5))]
            us = [[rng.randrange(p) for _ in grid] for grid in points]
            for u in us:
                u[:] = add([], u, p)
            unsat, _, _ = check_instance(points, us, rng.randrange(p), p)
            if unsat:
                certificates += 1
            else:
                zeros += 1
    print(f"Checked 500 mixed-grid instances: {certificates} certificates and {zeros} grid zeros.")
    p = 1009
    for m in range(1, 5):
        weights = [pow(2, j, p) for j in range(m)]
        us = [[0, a] for a in weights + [pow(2, -1, p)] + weights]
        b = (37 - (2 ** m - 1)) % p
        assert check_instance([[0, 1]] * (2 * m + 1), us, b, p) == (True, 2 ** m, 3 * 2 ** m)
    print("Verified sharp interleaved width 3r for r = 2, 4, 8, 16 over F_1009.")
    count = check_orders(rng)
    print(f"Verified {count} order decisions, with exhaustive orders or multiplicity restoration.")


if __name__ == "__main__":
    main()
