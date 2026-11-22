"""Small exact controls for composition-factor determinants and orbit counts."""

from itertools import permutations, product
from math import gcd, prod


def operations(q):
    if q != 4:
        return lambda a, b: (a + b) % q, lambda a, b: a * b % q, lambda a: -a % q

    def multiply(a, b):
        value = 0
        while b:
            if b & 1:
                value ^= a
            b >>= 1
            a <<= 1
            if a & 4:
                a ^= 7
        return value

    return lambda a, b: a ^ b, multiply, lambda a: a


def power(a, n, multiply):
    result = 1
    for _ in range(n):
        result = multiply(result, a)
    return result


def determinant(matrix, q, ops):
    add, multiply, neg = ops
    size = len(matrix)
    rows = [row[:] for row in matrix]
    result = 1
    for col in range(size):
        pivot = next((r for r in range(col, size) if rows[r][col]), None)
        if pivot is None:
            return 0
        if pivot != col:
            rows[col], rows[pivot] = rows[pivot], rows[col]
            result = neg(result)
        leading = rows[col][col]
        result = multiply(result, leading)
        inverse = power(leading, q - 2, multiply)
        for r in range(col + 1, size):
            factor = multiply(rows[r][col], inverse)
            if factor:
                for c in range(col + 1, size):
                    rows[r][c] = add(rows[r][c], neg(multiply(factor, rows[col][c])))
    return result


def truncated_auto_determinants(q, bounds):
    ops = operations(q)
    add, multiply, _ = ops
    arity = len(bounds)
    monomials = list(product(*(range(bound) for bound in bounds)))
    zero_exp = monomials[0]
    linear = list(reversed(sorted(x for x in monomials if sum(x) == 1)))

    def poly_mul(left, right):
        output = {}
        for a, u in left.items():
            for b, v in right.items():
                c = tuple(x + y for x, y in zip(a, b))
                if all(x < bound for x, bound in zip(c, bounds)):
                    output[c] = add(output.get(c, 0), multiply(u, v))
        return {m: c for m, c in output.items() if c}

    def substituted_det(images):
        basis_powers = []
        for image, bound in zip(images, bounds):
            row = [{zero_exp: 1}]
            for _ in range(1, bound):
                row.append(poly_mul(row[-1], image))
            assert not poly_mul(row[-1], image)
            basis_powers.append(row)
        columns = []
        for exponent in monomials:
            image = {zero_exp: 1}
            for i, k in enumerate(exponent):
                image = poly_mul(image, basis_powers[i][k])
            columns.append([image.get(m, 0) for m in monomials])
        return determinant([list(row) for row in zip(*columns)], q, ops)

    found = set()
    checked = 0
    for coeffs in product(range(q), repeat=arity * arity):
        tangent = [list(coeffs[j:j+arity]) for j in range(0, len(coeffs), arity)]
        if any(tangent[i][j] and bounds[i] < bounds[j] for i in range(arity) for j in range(arity)):
            continue
        if not determinant(tangent, q, ops):
            continue
        images = [{m: c for m, c in zip(linear, row) if c} for row in tangent]
        result = substituted_det(images)
        assert result
        found.add(result)
        checked += 1
    # Nonlinear automorphisms with identity tangent add independent higher terms.
    for i, bound in enumerate(bounds):
        if bound <= 2:
            continue
        images = [{m: 1} for m in linear]
        images[i][tuple(2 * x for x in linear[i])] = 1
        assert substituted_det(images) == 1
        checked += 1
    exponent = gcd(*(prod(bounds) * (bound - 1) // 2 for bound in bounds))
    assert found == {power(a, exponent, multiply) for a in range(1, q)}
    return len(found), checked


def group_regular_determinants(q):
    group = list(permutations(range(3)))
    position = {g: i for i, g in enumerate(group)}
    table = [[position[tuple(g[h[i]] for i in range(3))] for h in group] for g in group]
    ops = operations(q)
    side = len(group)
    found_left, found_right = set(), set()
    units = 0
    for coeffs in product(range(q), repeat=side):
        left = [[0] * side for _ in group]
        right = [[0] * side for _ in group]
        for i, weight in enumerate(coeffs):
            for j in range(side):
                left[table[i][j]][j] = weight
                right[table[j][i]][j] = weight
        a = determinant(left, q, ops)
        b = determinant(right, q, ops)
        assert bool(a) == bool(b)
        if a:
            units += 1
            found_left.add(a)
            found_right.add(b)
    assert found_left == found_right == set(range(1, q))
    return units


def compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for tail in compositions(total - first, length - 1):
            yield (first,) + tail


def square_zero_spectrum():
    checks = 0
    for n in range(3, 9):
        present = {d: set() for d in range(1, n + 1) if n % d == 0}
        for v in range(1, n):
            for blocks in compositions(n - v, v * v):
                rows = [1 + sum(blocks[i*v:(i+1)*v]) for i in range(v)]
                cols = [1 + sum(blocks[j::v]) for j in range(v)]
                for d, values in present.items():
                    values.add(gcd(d, *rows) * gcd(d, *cols))
                checks += 1
        for d, values in present.items():
            expected = {t for t in range(1, d*d+1) if d*d % t == 0}
            if d == n:
                expected -= {n*n//p for p in range(2, n+1) if n % p == 0
                             and all(p % k for k in range(2, p))}
            assert values == expected, (n, d, values)
    return checks


def main():
    for field, bounds in [(4, (2, 2)), (4, (4, 4)), (4, (8, 2)), (3, (3, 9)), (5, (5, 5))]:
        size, checked = truncated_auto_determinants(field, bounds)
        print(f"q={field}, bounds={bounds}: {checked} substitutions, {(field-1)//size} orbit classes")
    for field in (3, 4):
        print(f"S3 regular matrices over F_{field}: {group_regular_determinants(field)} units")
    print(f"Sharp square-zero spectra checked on {square_zero_spectrum()} radical dimension matrices.")


if __name__ == "__main__":
    main()
