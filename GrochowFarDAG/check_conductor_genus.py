"""Finite exact controls for ConductorGenus.md, using the standard library."""
from fractions import Fraction
from itertools import permutations
from math import prod


def coordinates(n):
    return [None, *((i, j) for i in range(n) for j in range(n) if i != j)]


def edge_values(labels, edges):
    return [2 if pair is not None and frozenset(pair) in edges else 1
            for pair in labels]


def lattice_basis(labels, a):
    rules = [{} for _ in labels]
    for prime, part in [(2, 0), (3, 1)]:
        reps = {}
        for i, pair in enumerate(labels):
            block = None if pair is None else pair[part]
            rep = reps.setdefault(block, i)
            if rep != i:
                rules[i][prime] = (rep, 1)
    for i in range(1, len(labels)):
        rules[i][5] = (0, a[i])
    columns = []
    for j, prescribed in enumerate(rules):
        col = [0] * j + [prod(prescribed)]
        for i in range(j + 1, len(labels)):
            residues = {
                p: col[rules[i][p][0]] * rules[i][p][1] % p if p in rules[i] else 0
                for p in (2, 3, 5)}
            col.append(next(x for x in range(30)
                            if all(x % p == r for p, r in residues.items())))
        columns.append(col)
    return columns


def solve(columns, v):
    coefficients = []
    for i, col in enumerate(columns):
        val = v[i] - sum(coefficients[j] * columns[j][i] for j in range(i))
        coefficients.append(Fraction(val, col[i]))
    return coefficients


def product(x, y):
    return [a * b for a, b in zip(x, y)]


def mapped_edges(edges, perm):
    return {frozenset(perm[v] for v in e) for e in edges}


def parity(perm):
    return sum(perm[i] > perm[j] for i in range(len(perm))
               for j in range(i + 1, len(perm))) % 2


def tensor_coeffs(order_basis, ideal_basis):
    coeffs = [
        [solve(ideal_basis, product(x, y)) for y in ideal_basis]
        for x in order_basis]
    assert all(c.denominator == 1 for row in coeffs for column in row for c in column)
    return [[[int(c) for c in col] for col in row] for row in coeffs]


def mod_fraction(x, modulus):
    return x.numerator * pow(x.denominator, -1, modulus) % modulus


def check_local(labels, a, modulus, prime):
    order_basis = lattice_basis(labels, [1] * len(labels))
    ideal_basis = lattice_basis(labels, a)
    source = tensor_coeffs(order_basis, order_basis)
    target = tensor_coeffs(order_basis, ideal_basis)
    b = [1] * len(labels)
    if prime == 5:
        lam = next(k for k in range(1, 5)
                   if pow(k, len(a), 5) * prod(a) % 5 == 1)
        b = [lam * v % 5 for v in a]
        b[-1] = pow(prod(b[:-1]), -1, modulus * 5)
        assert b[-1] % 5 == lam * a[-1] % 5
    det = Fraction(prod(b) * prod(col[i] for i, col in enumerate(order_basis)),
                   prod(col[i] for i, col in enumerate(ideal_basis)))
    assert mod_fraction(det, modulus) == 1
    columns = [[mod_fraction(c, modulus)
                for c in solve(ideal_basis, product(b, col))]
               for col in order_basis]
    for i in range(len(labels)):
        for j in range(len(labels)):
            for k in range(len(labels)):
                lhs = sum(columns[e][k] * s for e, s in enumerate(source[i][j]))
                rhs = sum(v * target[i][e][k] for e, v in enumerate(columns[j]))
                assert (lhs - rhs) % modulus == 0


def main():
    labels = coordinates(4)
    path = {frozenset(e) for e in [(0, 1), (1, 2), (2, 3)]}
    star = {frozenset(e) for e in [(0, 1), (0, 2), (0, 3)]}
    for graph in (set(), path, star):
        for prime, modulus in [(2, 8), (3, 27), (5, 125), (7, 49)]:
            check_local(labels, edge_values(labels, graph), modulus, prime)

    for n in range(3, 8):
        labels = coordinates(n)
        positions = {pair: i for i, pair in enumerate(labels)}
        for perm in permutations(range(n)):
            flags = [0, *(positions[(perm[i], perm[j])] for i, j in labels[1:])]
            assert parity(flags) == parity(perm)
    asymmetric = {frozenset(e) for e in [(0, 1), (0, 2), (2, 3),
                                          (0, 4), (4, 5), (5, 6)]}
    odd = (1, 0, 2, 3, 4, 5, 6)
    relabeled = mapped_edges(asymmetric, odd)
    perms = list(p for p in permutations(range(7))
                 if mapped_edges(asymmetric, p) == relabeled)
    assert perms == [odd] and parity(odd) == 1
    assert len(list(p for p in permutations(range(4)) if mapped_edges(path, p) == star)) == 0
    print("12 local determinant-one comparisons and all flag signs for n=3..7 passed")
    print("explicit asymmetric seven-vertex parity witness and nonisomorphic control passed")


if __name__ == "__main__":
    main()

