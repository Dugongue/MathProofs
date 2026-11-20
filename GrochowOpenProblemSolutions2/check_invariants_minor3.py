"""Exact rational and finite-field controls for the third-minor rank formula."""

from collections import defaultdict
from fractions import Fraction
from itertools import combinations, combinations_with_replacement, permutations
from math import comb


def unit_monomial(d, i, power=1):
    return tuple(power if j == i else 0 for j in range(d))


def multiply(a, b):
    return tuple(x + y for x, y in zip(a, b))


def divide(a, b):
    return tuple(x - y for x, y in zip(a, b))


def collect(column, key, delta):
    val = column.get(key, 0) + delta
    if val:
        column[key] = val
    else:
        column.pop(key, None)


def add_column(pivots, column, prime=None):
    if prime is not None:
        column = {key: val % prime for key, val in column.items() if val % prime}
    while column:
        first = min(column)
        coefficient = column[first]
        if first not in pivots:
            if prime is None:
                pivots[first] = {
                    key: Fraction(val, coefficient) for key, val in column.items()
                }
            else:
                inverse = pow(coefficient, -1, prime)
                pivots[first] = {
                    key: val * inverse % prime for key, val in column.items()
                }
            return
        for key, val in pivots[first].items():
            result = column.get(key, 0) - coefficient * val
            if prime is not None:
                result %= prime
            if result:
                column[key] = result
            else:
                column.pop(key, None)


def minor3_rank(multiplication, prime):
    triples = list(combinations(range(len(multiplication)), 3))
    pivot_polynomials = {}
    permutations_with_sign = [
        (perm, -1 if sum(perm[i] > perm[j] for i, j in combinations(range(3), 2)) % 2 else 1)
        for perm in permutations(range(3))
    ]
    for rows, cols in combinations_with_replacement(triples, 2):
        minor = {}
        for perm, sign in permutations_with_sign:
            term = [multiplication[rows[i]][cols[perm[i]]] for i in range(3)]
            if None not in term:
                collect(minor, tuple(sorted(term)), sign)
        add_column(pivot_polynomials, minor, prime)
    return len(pivot_polynomials)


class ConnectedSum:
    """The algebra with mixed products zero and all top powers identified."""

    def __init__(self, exponents):
        self.exponents = exponents
        self.d = len(exponents)
        self.zero = (0,) * self.d
        self.socle = unit_monomial(self.d, self.d - 1, exponents[-1])
        self.basis = [self.zero] + [
            unit_monomial(self.d, i, power)
            for i in range(self.d)
            for power in range(1, exponents[i])
        ] + [self.socle]
        self.ids = {x: i for i, x in enumerate(self.basis)}
        self.n = len(self.basis)

    def normal(self, monomial):
        support = [i for i, v in enumerate(monomial) if v]
        if not support:
            return self.zero
        if len(support) > 1:
            return None
        i, = support
        power = monomial[i]
        if power < self.exponents[i]:
            return monomial
        if power == self.exponents[i]:
            return self.socle
        return None

    def groebner_basis(self):
        d = self.d
        units = [unit_monomial(d, i) for i in range(d)]
        return [
            (multiply(a, b), None) for a, b in combinations(units, 2)
        ] + [
            (unit_monomial(d, i, self.exponents[i]), self.socle)
            for i in range(d - 1)
        ] + [(unit_monomial(d, d - 1, self.exponents[-1] + 1), None)]

    def syzygies(self):
        groebner = self.groebner_basis()
        pivots = {}
        for i, j in combinations(range(len(groebner)), 2):
            m_i, n_i = groebner[i]
            m_j, n_j = groebner[j]
            lcm = tuple(max(a, b) for a, b in zip(m_i, m_j))
            c_i, c_j = divide(lcm, m_i), divide(lcm, m_j)
            syzygy = [(i, c_i, 1), (j, c_j, -1)]
            # Compute the two reductions separately. Their normal forms coincide.
            for tail, factor, sign in ((n_i, c_i, -1), (n_j, c_j, 1)):
                if tail is None:
                    continue
                monomial = multiply(tail, factor)
                while True:
                    for index, (leading, rest) in enumerate(groebner):
                        quotient = divide(monomial, leading)
                        if min(quotient) >= 0:
                            syzygy.append((index, quotient, -sign))
                            if rest is not None:
                                monomial = multiply(quotient, rest)
                            break
                    else:
                        break
                    if rest is None:
                        break
            yield syzygy

    def conormal_dimension(self, prime):
        pivots = {}
        for syzygy in self.syzygies():
            for monomial in self.basis:
                column = {}
                for index, factor, sign in syzygy:
                    coefficient = self.normal(multiply(factor, monomial))
                    if coefficient is not None:
                        collect(column, (index, coefficient), sign)
                add_column(pivots, column, prime)
        return len(self.groebner_basis()) * self.n - len(pivots)

    def minor3_rank(self, prime):
        multiplication = [
            [self.ids.get(self.normal(multiply(x, y))) for y in self.basis]
            for x in self.basis
        ]
        return minor3_rank(multiplication, prime)


def main():
    for prime in (None, 3, 5):
        cases = 0
        for dimension in range(2, 6):
            for exponents in combinations_with_replacement(range(2, 7), dimension):
                algebra = ConnectedSum(exponents)
                if algebra.n > 14:
                    continue
                conormal = algebra.conormal_dimension(prime)
                rank = algebra.minor3_rank(prime)
                n = algebra.n
                predicted = comb(n, 3) + n * dimension - conormal
                assert rank == predicted, (prime, exponents, conormal, rank, predicted)
                cases += 1

        for d in range(2, 9):
            n = d + 1
            multiplication = [
                [j if i == 0 else i if j == 0 else None for j in range(n)]
                for i in range(n)
            ]
            # For I = m^2 the conormal space is m^2/m^4.
            conormal = comb(d + 1, 2) + comb(d + 2, 3)
            rank = minor3_rank(multiplication, prime)
            predicted = comb(n, 3) + n * d - conormal
            assert rank == predicted, (prime, d, conormal, rank, predicted)
            cases += 1

        label = "Q" if prime is None else f"F_{prime}"
        print(f"{label}: passed {cases} exact conormal-rank checks", flush=True)


if __name__ == "__main__":
    main()
