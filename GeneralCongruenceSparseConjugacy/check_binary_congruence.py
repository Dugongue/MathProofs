"""Direct ordinary-PC computations on raw binary matrix equations."""

from collections import deque
from itertools import combinations_with_replacement, product


def bit_polynomial(terms, constant=False):
    support = {()} if constant else set()
    for monomial in terms:
        support.symmetric_difference_update((tuple(sorted(monomial)),))
    return frozenset(support)


class TruncatedPC:
    def __init__(self, variables, degree):
        self.variables = variables
        self.degree = degree
        self.monomials = [m for d in range(degree + 1)
                          for m in combinations_with_replacement(range(variables), d)]
        self.index = {m: i for i, m in enumerate(self.monomials)}
        self.lower_cutoff = sum(len(m) < degree for m in self.monomials)
        self.shifts = [[self.index[tuple(sorted(m + (x,)))]
                        for m in self.monomials[:self.lower_cutoff]] for x in range(variables)]

    def refutes(self, equations):
        todo = deque()
        for polynomial in equations:
            if all(len(m) <= self.degree for m in polynomial):
                todo.append(sum(1 << self.index[m] for m in polynomial))
        basis = {}
        while todo:
            row = todo.popleft()
            while row:
                pivot = row.bit_length() - 1
                if pivot in basis:
                    row ^= basis[pivot]
                    continue
                if pivot == 0:
                    return True
                basis[pivot] = row
                if pivot < self.lower_cutoff:
                    support = []
                    bits = row
                    while bits:
                        low = bits & -bits
                        support.append(low.bit_length() - 1)
                        bits ^= low
                    for shift in self.shifts:
                        todo.append(sum(1 << shift[i] for i in support))
                break
        return False


def gram_equations(a, b):
    def x(i, j):
        return 2 * i + j

    def y(i, j):
        return 4 + 2 * i + j

    for i, j in product(range(2), repeat=2):
        yield bit_polynomial(((x(i, h), x(j, l))
                              for h, l in product(range(2), repeat=2) if a[2*h + l]),
                             b[2*i + j])
        yield bit_polynomial(((x(i, h), y(h, j)) for h in range(2)), i == j)
        yield bit_polynomial(((y(i, h), x(h, j)) for h in range(2)), i == j)


def symplectic_equations(u, v):
    r, s = 2*u, 2*v
    for i, j in product(range(s), repeat=2):
        yield bit_polynomial(((r*i + h, r*j + (h ^ 1)) for h in range(r)), (i ^ 1) == j)
    for i, j in product(range(r), repeat=2):
        yield bit_polynomial(((r*h + i, r*(h ^ 1) + j) for h in range(s)), (i ^ 1) == j)


def gf4_product(a, b):
    acc = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    return acc ^ 7 if acc & 4 else acc


def gf4_gram(a, x):
    out = []
    for i, j in product(range(2), repeat=2):
        v = 0
        for h, l in product(range(2), repeat=2):
            if a[2*h + l]:
                v ^= gf4_product(x[2*i + h], x[2*j + l])
        out.append(v)
    return tuple(out)


def kind(a):
    if not any(a):
        return 0
    if a[1] == a[2]:
        return 2 if a[0] or a[3] else 1
    return 3


def verify_raw():
    invertible = [x for x in product(range(4), repeat=4)
                  if gf4_product(x[0], x[3]) != gf4_product(x[1], x[2])]
    forms = list(product((0, 1), repeat=4))
    engines = {d: TruncatedPC(8, d) for d in (0, 2, 3)}
    counts = {}
    for a in forms:
        orbit = {gf4_gram(a, x) for x in invertible}
        for b in forms:
            expected = None
            if b not in orbit:
                if (not any(a) and any(b)) or (kind(a) == 1 and (b[0] or b[3])):
                    expected = 0
                elif kind(b) > kind(a):
                    expected = 2
                else:
                    expected = 3
            equations = list(gram_equations(a, b))
            got = next((d for d, engine in engines.items() if engine.refutes(equations)), None)
            assert got == expected, (a, b, got, expected)
            counts[got] = counts.get(got, 0) + 1
    return counts


if __name__ == "__main__":
    print("All 256 ordered binary 2-by-2 pairs, grouped by degree:", verify_raw())
    for u, v, lo, hi in [(1, 2, 1, 2), (1, 3, 2, 3), (2, 3, 1, 2)]:
        eq = list(symplectic_equations(u, v))
        assert not TruncatedPC(4*u*v, lo).refutes(eq)
        assert TruncatedPC(4*u*v, hi).refutes(eq)
    hard = list(symplectic_equations(2, 4))
    assert not TruncatedPC(32, 3).refutes(hard)
    print("Verified three exact symplectic rectangle degrees and the degree-four lower bound for (2,4).")
