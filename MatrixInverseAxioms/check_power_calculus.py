"""Exact controls for binary-power proof lines and the finite moment lemma."""

from itertools import combinations, product
from random import Random


def matrix_add(a, b):
    return [[(x + y) % prime for x, y in zip(u, v)] for u, v in zip(a, b)]


def matrix_sub(a, b):
    return [[(x - y) % prime for x, y in zip(u, v)] for u, v in zip(a, b)]


def matrix_product(a, b):
    return [[sum(x * y for x, y in zip(row, col)) % prime for col in zip(*b)] for row in a]


def trace(a):
    return sum(a[i][i] for i in range(len(a))) % prime


def power_moments(diag_a, diag_b):
    support = sorted(set(diag_a) | set(diag_b))
    weights = [diag_a.count(x) - diag_b.count(x) for x in support]
    moments = [sum(w * x ** k for w, x in zip(weights, support)) % prime
               for k in range(len(support))]
    assert any(w % prime for w in weights) == any(moments)


def check_power(a, b, x, y, k):
    identity = [[int(i == j) for j in range(len(a))] for i in range(len(a))]

    def mismatch(left, right):
        return matrix_sub(matrix_product(x, left), matrix_product(right, x))

    def combine(first, second):
        f_a, f_b, h_f = first
        g_a, g_b, h_g = second
        fg_a, fg_b = matrix_product(f_a, g_a), matrix_product(f_b, g_b)
        h_fg = matrix_add(matrix_product(h_f, g_a), matrix_product(f_b, h_g))
        assert h_fg == mismatch(fg_a, fg_b)
        return fg_a, fg_b, h_fg

    current = (identity, identity, mismatch(identity, identity))
    next_power = (a, b, mismatch(a, b))
    for exponent in range(k.bit_length()):
        if k & (1 << exponent):
            current = combine(current, next_power)
        next_power = combine(next_power, next_power)
    ka, kb, h = current
    first = matrix_product(ka, matrix_sub(identity, matrix_product(y, x)))
    second = matrix_product(kb, matrix_sub(identity, matrix_product(x, y)))
    third = matrix_product(y, h)
    assert (trace(ka) - trace(kb)) % prime == (trace(first) - trace(second) + trace(third)) % prime


def nonzero_projection(points, weights, coordinates, p):
    mass = {}
    for point, weight in zip(points, weights):
        key = tuple(point[i] for i in coordinates)
        mass[key] = (mass.get(key, 0) + weight) % p
    return any(mass.values())


random = Random(73)
matrix_cases = 0
moment_cases = 0
for prime in (2, 3, 5, 101):
    for size in range(1, 8):
        for k in (1, 2, 3, 5, 2 * size - 1, 37):
            matrices = [[[random.randrange(prime) for _ in range(size)] for _ in range(size)]
                        for _ in range(4)]
            check_power(*matrices, k)
            power_moments(*[[random.randrange(prime) for _ in range(size)] for _ in range(2)])
            matrix_cases += 1

for p, dimensions, alphabet in ((2, 3, 2), (3, 3, 2), (2, 2, 3)):
    points = list(product(range(alphabet), repeat=dimensions))
    for weights in product(range(p), repeat=len(points)):
        support = sum(w != 0 for w in weights)
        if support == 0:
            continue
        bound = support.bit_length() - 1
        assert any(nonzero_projection(points, weights, coords, p)
                   for j in range(bound + 1)
                   for coords in combinations(range(dimensions), j))
        moment_cases += 1

print(f"Verified {matrix_cases} exact power and trace computations and "
      f"{moment_cases} finite signed-measure support cases.")
