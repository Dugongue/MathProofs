from collections import Counter
from fractions import Fraction
from functools import cache
from itertools import combinations
from math import comb
from random import Random


def polynomial_divide_monic(dividend, divisor):
    remainder = list(dividend) + [0] * max(0, len(divisor) - 1 - len(dividend))
    quotient = [0] * max(0, len(dividend) - len(divisor) + 1)
    for shift in range(len(quotient) - 1, -1, -1):
        coefficient = remainder[shift + len(divisor) - 1]
        quotient[shift] = coefficient
        for j, entry in enumerate(divisor):
            remainder[shift + j] -= coefficient * entry
    return tuple(quotient), tuple(remainder[:len(divisor) - 1])


@cache
def cyclotomic(n):
    polynomial = (-1,) + (0,) * (n - 1) + (1,)
    for divisor in range(1, n):
        if n % divisor == 0:
            polynomial, remainder = polynomial_divide_monic(polynomial, cyclotomic(divisor))
            assert not any(remainder)
    return polynomial


def check_root_sets(n):
    phi = cyclotomic(n)
    roots = [polynomial_divide_monic((0,) * i + (1,), phi)[1] for i in range(n)]
    differences = Counter(tuple(a - b for a, b in zip(first, second))
                          for i, first in enumerate(roots)
                          for j, second in enumerate(roots) if i != j)
    assert len(set(roots)) == n
    assert max(differences.values()) <= (2 if n % 2 == 0 else 1)
    largest = Fraction(0)
    for size in range(1, n):
        zeros = sum(all(total == 0 for total in map(sum, zip(*subset)))
                    for subset in combinations(roots, size))
        if size in (1, n - 1):
            assert zeros == 0
        frequency = Fraction(zeros, comb(n, size))
        if n % 2 == 0:
            assert frequency <= Fraction(1, n - 1)
        else:
            assert frequency < Fraction(1, n - 1)
        largest = max(frequency, largest)
    return largest


def determinant(matrix):
    rows = [list(map(Fraction, row)) for row in matrix]
    answer = Fraction(1)
    for i in range(len(rows)):
        pivot = next((j for j in range(i, len(rows)) if rows[j][i]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != i:
            rows[i], rows[pivot] = rows[pivot], rows[i]
            answer = -answer
        answer *= rows[i][i]
        for j in range(i + 1, len(rows)):
            factor = rows[j][i] / rows[i][i]
            rows[j] = [x - factor * y for x, y in zip(rows[j], rows[i])]
    return answer


def pfaffian(matrix):
    @cache
    def expansion(indices):
        if not indices:
            return 1
        first, *rest = indices
        return sum((-1) ** j * matrix[first][index] * expansion(tuple(rest[:j] + rest[j + 1:]))
                   for j, index in enumerate(rest))
    return expansion(tuple(range(len(matrix))))


def check_pfaffians():
    sampler = Random(143)
    cases = 0
    for n in range(4, 13, 2):
        for modulus in (None, 2, 3, 5):
            for _ in range(6):
                matrix = [[sampler.randrange(-3, 4) if modulus is None else sampler.randrange(modulus)
                           for _ in range(n)] for _ in range(n)]
                alternating = [[sum(matrix[k][i] * matrix[k + 1][j] - matrix[k + 1][i] * matrix[k][j]
                                    for k in range(0, n, 2))
                                for j in range(n)] for i in range(n)]
                direct = determinant(matrix)
                expanded = pfaffian(alternating)
                if modulus is None:
                    assert direct == expanded
                else:
                    assert direct.denominator == 1
                    assert (direct.numerator - expanded) % modulus == 0
                cases += 1
    return cases


if __name__ == "__main__":
    frequencies = [f"{n}:{check_root_sets(n)}" for n in range(2, 17)]
    print("Maximum exact zero-sum frequencies by size n: " + ", ".join(frequencies))
    print(f"Pfaffian and independent determinant evaluations matched on {check_pfaffians()} matrices")
