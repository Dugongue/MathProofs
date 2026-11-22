"""Direct PC span checks in two variables per matrix direction and Pfaffian identity tests."""

from itertools import combinations, combinations_with_replacement
from random import Random


def add_term(poly, monomial, coefficient, prime):
    monomial = tuple(sorted(monomial))
    value = (poly.get(monomial, 0) + coefficient) % prime
    if value:
        poly[monomial] = value
    else:
        poly.pop(monomial, None)


def congruence_refutes(a, b, prime, degree):
    side = len(a)
    variables = 2 * side ** 2
    def x(i, j):
        return side * i + j
    def y(i, j):
        return side ** 2 + side * i + j
    inputs = []
    for i in range(side):
        for j in range(side):
            gram, xy, yx = {}, {}, {}
            add_term(gram, (), -b[i][j], prime)
            add_term(xy, (), -(i == j), prime)
            add_term(yx, (), -(i == j), prime)
            for u in range(side):
                for v in range(side):
                    add_term(gram, (x(i, u), x(j, v)), a[u][v], prime)
                add_term(xy, (x(i, u), y(u, j)), 1, prime)
                add_term(yx, (y(i, u), x(u, j)), 1, prime)
            inputs.extend((gram, xy, yx))
    monomials = [m for d in range(degree + 1)
                 for m in combinations_with_replacement(range(variables), d)]
    index = {m: i for i, m in enumerate(monomials)}
    queue = [{index[m]: c for m, c in line.items()}
             for line in inputs if all(len(m) <= degree for m in line)]
    basis = {}
    while queue:
        row = queue.pop()
        while row:
            lead = max(row)
            if lead not in basis:
                break
            scale = row[lead]
            for pos, value in basis[lead].items():
                new = (row.get(pos, 0) - scale * value) % prime
                if new:
                    row[pos] = new
                else:
                    row.pop(pos, None)
        if not row:
            continue
        if lead == 0:
            return True
        inv = pow(row[lead], -1, prime)
        norm = {i: c * inv % prime for i, c in row.items()}
        basis[lead] = norm
        if len(monomials[lead]) < degree:
            for v in range(variables):
                queue.append({index[tuple(sorted((*monomials[i], v)))]: c
                              for i, c in norm.items()})
    return False


def determinant(a, prime):
    a = [r[:] for r in a]
    value = 1
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j] % prime), None)
        if pivot is None:
            return 0
        if j != pivot:
            a[pivot], a[j] = a[j], a[pivot]
            value *= -1
        value = value * a[j][j] % prime
        inv = pow(a[j][j] % prime, -1, prime)
        for i in range(j + 1, len(a)):
            factor = a[i][j] * inv % prime
            for k in range(j, len(a)):
                a[i][k] = (a[i][k] - factor * a[j][k]) % prime
    return value


def pfaffian(gram, indices, prime):
    if not indices:
        return 1
    return sum((-1) ** (i + 1) * gram[indices[0]][indices[i]]
               * pfaffian(gram, indices[1:i] + indices[i + 1:], prime)
               for i in range(1, len(indices))) % prime


def pfaffian_checks():
    rng = Random(120197)
    tests = 0
    for prime in (2, 3, 5):
        for a in range(1, 7):
            rows = [[rng.randrange(prime) for _ in range(2*a)] for _ in range(a+1)]
            gram = [[sum(u[2*i] * v[2*i+1] - u[2*i+1] * v[2*i] for i in range(a))
                     for v in rows] for u in rows]
            for j in range(1, (a+1)//2+1):
                for picks in combinations(range(a+1), 2*j):
                    value = 0
                    for slots in combinations(range(a), j):
                        columns = [c for t in slots for c in (2*t, 2*t+1)]
                        value += determinant([[rows[i][c] for c in columns] for i in picks], prime)
                    assert value % prime == pfaffian(gram, picks, prime)
                    tests += 1
    return tests


def main():
    zero = [[0, 0], [0, 0]]
    sym = [[1, 0], [0, 0]]
    alt = [[0, 1], [-1, 0]]
    mixed = [[0, 1], [-1, 1]]
    singular = [[0, 1], [0, 0]]
    tests = 0
    for p in (3, 5, 7):
        examples = [(zero, sym, 0), (alt, mixed, 0), (alt, singular, 2),
                    (sym, alt, 2), (mixed, alt, 3), (mixed, singular, 3),
                    (singular, mixed, 3), (singular, zero, 3),
                    (sym, sym, None), (mixed, mixed, None)]
        for a, b, exact in examples:
            for degree in (0, 1, 2, 3):
                assert congruence_refutes(a, b, p, degree) == (exact is not None and degree >= exact)
                tests += 1
    print(f"Verified {tests} direct bounded-degree PC spans and {pfaffian_checks()} Pfaffian identities.")


if __name__ == "__main__":
    main()
