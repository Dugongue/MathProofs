"""Exact arithmetic checks for the degree-eight Kempf construction."""

from fractions import Fraction
from math import gcd


def monomial(m, *factors):
    result = [0] * (2 * (m + 1))
    for is_y, index, exponent in factors:
        result[index + is_y * (m + 1)] += exponent
    return tuple(result)


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True))


def check(m):
    pairs = [monomial(m, (0, j, 4), (1, j, 4)) for j in range(m + 1)]
    steps = []
    for j in range(1, m):
        steps.append(monomial(m, (0, j + 1, 2), (1, j, 4), (0, 0, 2)))
        steps.append(monomial(m, (1, j + 1, 2), (0, j, 4), (1, 0, 2)))
    terminal = monomial(m, (0, 1, 2), (1, 0, 2), (0, m, 2), (1, m, 2))
    support = pairs + steps + [terminal]
    assert len(set(support)) == len(support) == 3 * m
    characters = [(j, phase) for phase in [1, 3] for j in range(m + 1)]
    assert len(set(characters)) == 2 * (m + 1)
    for exp in support:
        assert sum(exp) == 8
        assert all((exp[j] + exp[j + m + 1]) % 2 == 0 for j in range(m + 1))
        assert sum(power * phase for power, (_, phase) in zip(exp, characters, strict=True)) % 4 == 0

    degree_balance = 2 * m + 6
    squared_coefficients = [Fraction(degree_balance - sum(exp[j] for exp in steps), 4)
                            for j in range(m + 1)] + [1] * len(steps)
    assert min(squared_coefficients) > 0
    assert all(dot(powers, squared_coefficients) == degree_balance
               for powers in zip(*(pairs + steps), strict=True))

    b = [0] + [2 ** j for j in range(m)]
    base = b + [-value for value in b]
    assert all(dot(exp, base) == 0 for exp in pairs + steps)
    assert dot(terminal, base) == 2

    divisor = gcd(sum(b), m + 1)
    a, d = -sum(b) // divisor, (m + 1) // divisor
    u = [a + d * value for value in b]
    weights = u + [-value for value in u]
    assert gcd(*weights) == 1
    assert sum(u) == 0
    assert all(dot(exp, weights) == 0 for exp in pairs + steps)
    assert dot(terminal, weights) == 2 * d
    diameter = max(weights) - min(weights)
    assert diameter == 2 * ((m - 1) * 2 ** (m - 1) + 1) // divisor
    assert diameter >= 2 ** (m - 1)

    objective = Fraction((2 * d) ** 2, 2 * dot(u, u))
    for gap in range(1, 7):
        for offset in range(-20, 21):
            trial = [offset + gap * value for value in b]
            assert Fraction((2 * gap) ** 2, 2 * dot(trial, trial)) <= objective
    return diameter


if __name__ == "__main__":
    assert __debug__
    for m in range(1, 33):
        last = check(m)
    print(f"32 forms checked. Last primitive eigenweight diameter {last}.")
