"""Exact certificate for the fixed four-mode marker over F_5."""
from itertools import product

L = 11
TARGET = (0, 8, 4, 0)
EXPECTED = [
    [0, 4, 4, 4, 3, 1, 4, 3, 3, 4, 1],
    [4, 2, 4, 2, 2, 4, 2, 2, 0, 1, 3],
    [2, 3, 1, 3, 0, 3, 2, 1, 1, 3, 2],
    [1, 3, 3, 3, 2, 2, 2, 0, 4, 4, 2],
]


def form_values(a, b):
    return (a, b, (a + b) % L, (a + 2 * b) % L)


def verify():
    state = 20261107
    exponents = []
    # Discard the first 121 values and keep the next 121.
    for i in range(2 * L * L):
        state = (1664525 * state + 1013904223) % 2**32
        if i >= L * L:
            exponents.append((state >> 16) % 4)
    result = [[0] * L for _ in range(4)]
    assignments = set()
    for a, b, u, v in product(range(L), repeat=4):
        s = (u, v, -u, -v)
        x = [(a - s[i] - s[(i + 1) % 4]) % L for i in range(4)]
        bp = [(b + s[(i + 1) % 4]) % L for i in range(4)]
        bm = [(b + s[i]) % L for i in range(4)]
        plus = tuple(zip(x, bp))
        minus = tuple(zip(x, bm))
        assignments.add((plus, minus))
        for i in range(4):
            for j, shift in enumerate((0, 1, 3, 2)):
                assert form_values(*plus[i])[j] == form_values(*minus[(i + shift) % 4])[j]
        exponent = sum(exponents[L * x[i] + bp[i]] - exponents[L * x[i] + bm[i]]
                       for i in range(4)) % 4
        weight = pow(2, exponent, 5)
        for row, label in zip(result, form_values(*plus[0])):
            row[label] = (row[label] + weight) % 5
    assert len(assignments) == L**4
    assert result == EXPECTED
    assert all(row.count(row[label]) == 1 for row, label in zip(result, TARGET))
    a, b, c, d = TARGET
    x, y = (c - a - b) % L, (d - a - 2 * b) % L
    assert x and y and y != x and y != 2 * x % L
    print("PASS: four selected marker eigenvalues are unique:", [row[i] for row, i in zip(result, TARGET)])


if __name__ == "__main__":
    verify()
