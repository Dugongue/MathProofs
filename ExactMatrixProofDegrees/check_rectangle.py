"""Exact small characteristic controls for rectangular inverse and matching design degree."""

from itertools import combinations, permutations
from collections import deque
from math import comb


def increment(line, index, value, prime):
    value = (line.get(index, 0) + value) % prime
    if value:
        line[index] = value
    else:
        line.pop(index, None)


class Echelon:
    def __init__(self, prime):
        self.p = prime
        self.basis = {}

    def insert(self, vector):
        line = vector.copy()
        while line:
            pivot = max(line)
            if pivot not in self.basis:
                inverse = pow(line[pivot], -1, self.p)
                row = {index: value * inverse % self.p for index, value in line.items()}
                self.basis[pivot] = row
                return pivot, row
            factor = line[pivot]
            for index, value in self.basis[pivot].items():
                increment(line, index, -factor * value, self.p)
        return None


def elementary_inverses(r, s, prime):
    """Entry vectors for both products on variables (P_ij,Q_ji) by edge."""
    def edge(i, j):
        return 2 * (i * s + j)

    def entry(terms, diagonal):
        polynomial = {(): prime - 1} if diagonal else {}
        for x, y in terms:
            monomial = tuple(sorted((x, y)))
            increment(polynomial, monomial, 1, prime)
        return polynomial

    for i in range(r):
        for j in range(r):
            yield entry(((edge(i, k) + 1, edge(j, k)) for k in range(s)), i == j)
    for i in range(s):
        for j in range(s):
            yield entry(((edge(k, i), edge(k, j) + 1) for k in range(r)), i == j)


def refutable(r, s, prime, bound):
    """Ordinary bounded PC saturation on actual monomials. No matching relations."""
    num_vars = 2 * r * s
    monomials = [()]
    layer = [()]
    for _ in range(bound):
        layer = [term + (variable,) for term in layer
                 for variable in range(term[-1] if term else 0, num_vars)]
        monomials.extend(layer)
    indices = {term: idx for idx, term in enumerate(monomials)}
    low_cutoff = comb(num_vars + bound - 1, bound - 1)
    queue = deque()
    if bound >= 2:
        for entry in elementary_inverses(r, s, prime):
            queue.append({indices[monomial]: value for monomial, value in entry.items()})
    basis = Echelon(prime)
    while queue:
        inserted = basis.insert(queue.popleft())
        if inserted is None:
            continue
        pivot, row = inserted
        if pivot == 0:
            return True
        if pivot < low_cutoff:
            for variable in range(num_vars):
                queue.append({indices[tuple(sorted(monomials[idx] + (variable,)))]: value
                              for idx, value in row.items()})
    return False


def valuation_power(gap, prime):
    value = 1
    while gap % prime == 0:
        gap //= prime
        value *= prime
    return value


def check_rectangles():
    cases = [(1, s, p) for s in range(2, 7) for p in (2, 3, 5)]
    cases += [(2, 3, 2), (2, 4, 2), (2, 4, 3), (2, 5, 3), (3, 4, 5), (3, 5, 2)]
    for r, s, p in cases:
        predicted = min(r + 2, 2 * valuation_power(s - r, p))
        assert not refutable(r, s, p, predicted - 1), (r, s, p, predicted)
        assert refutable(r, s, p, predicted), (r, s, p, predicted)
    return len(cases)


def design_rows(r, s, p, j):
    matchings = [()]
    for k in range(1, j + 1):
        matchings.extend(tuple(zip(rows, cols)) for rows in combinations(range(r), k)
                         for cols in permutations(range(s), k))
    keys = {matching: i for i, matching in enumerate(matchings)}
    equations = Echelon(p)
    for matching in matchings:
        if len(matching) == j:
            continue
        used_rows = dict(matching)
        used_cols = dict((b, a) for a, b in matching)
        for axis, amount, other in ((0, r, s), (1, s, r)):
            for i in range(amount):
                if i in (used_rows if axis == 0 else used_cols):
                    continue
                equation = {keys[matching]: p - 1}
                for v in range(other):
                    if v in (used_cols if axis == 0 else used_rows):
                        continue
                    edge = (i, v) if axis == 0 else (v, i)
                    bigger = tuple(sorted(matching + (edge,)))
                    increment(equation, keys[bigger], 1, p)
                equations.insert(equation)
    return equations, len(matchings)


def check_endpoint():
    cases = [(1, 3, 2, 1), (1, 4, 3, 1), (3, 6, 3, 2),
             (3, 7, 2, 2), (3, 8, 5, 2)]
    for r, s, p, j in cases:
        previous, cutoff = design_rows(r, s, p, j-1)
        current, _ = design_rows(r, s, p, j)
        assert 0 not in current.basis
        # Degree truncation is surjective iff there are no extra relations
        # on the lower coordinates after eliminating the upper coordinates.
        assert sum(i < cutoff for i in current.basis) == len(previous.basis)
    return len(cases)


if __name__ == "__main__":
    print(f"Checked normalization and extension on {check_endpoint()} endpoint design spaces.", flush=True)
    print(f"Checked both sides of exact ordinary PC degree on {check_rectangles()} rectangles.", flush=True)
