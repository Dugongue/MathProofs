"""Finite checks for the group coordinates and small-restriction lift."""
from itertools import combinations_with_replacement
from random import Random


def sparse_sum(left, right, prime, scale=1):
    out = dict(left)
    for key, value in right.items():
        new = (out.get(key, 0) + scale * value) % prime
        if new:
            out[key] = new
        else:
            out.pop(key, None)
    return out


def reduce_row(row, pivots, prime):
    for key, reducer in sorted(pivots.items()):
        if key in row:
            row = sparse_sum(row, reducer, prime, -row[key])
    return row


def row_basis(rows, prime):
    pivots = {}
    for row in rows:
        row = reduce_row(row, pivots, prime)
        if row:
            pivot = min(row)
            scale = pow(row[pivot], -1, prime)
            pivots[pivot] = {k: a * scale % prime for k, a in row.items()}
    return pivots


def pencil_space(copies, add_data):
    nx = 2 * copies
    first, second, data = {}, {}, {}
    for i in range(copies):
        x = 2 * i
        y = nx + 4 * i
        for j in range(2):
            first[x + j, y + j] = 1
            second[x + j, y + 2 + j] = 1
        data[x + 1, y] = 1
    return [first, second, data] if add_data else [first, second]


def quadratic(a, prime):
    out = {}
    for i, j in combinations_with_replacement(range(len(a)), 2):
        value = a[i] * a[j] if i != j else a[i] * (a[i] - 1) // 2
        if value % prime:
            out[i, j] = value % prime
    return out


def multiply(u, v, prime):
    out = {}
    for i, a in enumerate(u):
        if not a % prime:
            continue
        for j, b in enumerate(v):
            if b % prime:
                key = min(i, j), max(i, j)
                value = (out.get(key, 0) + a * b) % prime
                if value:
                    out[key] = value
                else:
                    out.pop(key, None)
    return out


def run(prime, exponent, generators):
    modulus = prime**exponent
    domain = 4 if modulus == 2 else modulus
    copies = 2 * generators + 1
    dimension = 6 * copies
    rng = Random(193)
    spaces = [pencil_space(copies, data) for data in (False, True)]
    quotient_bases = [row_basis(space, prime) for space in spaces]
    checked = 0
    if modulus == 2:
        squares = [{(i, i): 1} for i in range(dimension)]
        for basis in quotient_bases:
            assert len(row_basis([reduce_row(q, basis, prime) for q in squares], prime)) == dimension

    for _ in range(12):
        labels = [tuple(rng.randrange(domain) for _ in range(dimension))
                  for _ in range(generators)]
        a, b = labels[0], labels[-1]
        ab = tuple((x + y) % domain for x, y in zip(a, b))
        rhs = sparse_sum(quadratic(a, prime), quadratic(b, prime), prime)
        rhs = sparse_sum(rhs, multiply(a, b, prime), prime)
        assert rhs == quadratic(ab, prime)
        rows = [quadratic(u, prime) for u in labels]
        for u in labels:
            for j in range(dimension):
                row = {(min(i, j), max(i, j)): x % prime
                       for i, x in enumerate(u) if x % prime}
                rows.append(row)
        rank = len(row_basis(rows, prime))
        for space in spaces:
            assert len(row_basis(rows + space, prime)) == rank + len(space)
        checked += 1
    return checked


def main():
    checked = sum(run(p, e, h) for p, e in [(2, 1), (2, 2), (2, 3), (3, 1), (3, 2)]
                  for h in (1, 2))
    print(f"{checked} group expansions and {2 * checked} simultaneous lift-space rank checks")


if __name__ == "__main__":
    main()
