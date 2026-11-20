"""Finite controls for the rank estimate and nested Frobenius gate replacement."""

from itertools import product
from random import Random


def rank_mod(rows, p):
    matrix = [row[:] for row in rows]
    rank = 0
    for col in range(len(matrix[0])):
        pivot = next((i for i in range(rank, len(matrix)) if matrix[i][col] % p), None)
        if pivot is None:
            continue
        matrix[pivot], matrix[rank] = matrix[rank], matrix[pivot]
        scale = pow(matrix[rank][col] % p, -1, p)
        for i in range(rank + 1, len(matrix)):
            value = (matrix[i][col] * scale) % p
            matrix[i] = [(a - value * b) % p for a, b in zip(matrix[i], matrix[rank])]
        rank += 1
    return rank


def symmetrize(matrix, p):
    return [[(matrix[i][j] + matrix[j][i]) % p for j in range(len(matrix))]
            for i in range(len(matrix))]


def check_rank():
    cases = 0
    for field in (2, 3):
        for entries in product(range(field), repeat=9):
            matrix = [list(entries[i:i + 3]) for i in range(0, 9, 3)]
            symmetric = symmetrize(matrix, field)
            assert rank_mod(symmetric, field) <= 2 * rank_mod(matrix, field)
            if field == 3:
                half = [[2 * value % field for value in row] for row in symmetric]
                assert symmetrize(half, field) == symmetric
            cases += 1
    return cases


def check_gate_replacement():
    random = Random(177)
    cases = 0
    for prime in (2, 3, 5):
        for exponent in (1, 2):
            cutoff = prime ** exponent

            def add(left, right):
                return [(a + b) % prime for a, b in zip(left, right)]

            def multiply(left, right):
                return [sum(left[i] * right[k - i] for i in range(k + 1)) % prime
                        for k in range(cutoff)]

            def scalar(value):
                return [value % prime] + [0] * (cutoff - 1)

            def power(poly):
                result = scalar(1)
                for _ in range(cutoff):
                    result = multiply(result, poly)
                return result

            for _ in range(18):
                a, b, c = ([random.randrange(prime) for _ in range(cutoff)] for _ in range(3))
                first = power(add(multiply(a, b), c))
                original = add(power(multiply(add(a, first), c)), multiply(first, b))
                first_constant = scalar(pow((a[0] * b[0] + c[0]) % prime, cutoff, prime))
                second_constant = scalar(pow((a[0] + first_constant[0]) * c[0] % prime,
                                             cutoff, prime))
                replacement = add(second_constant, multiply(first_constant, b))
                assert original == replacement
                cases += 1
    return cases


if __name__ == "__main__":
    print(f"Rank bound and section: {check_rank()} matrices.")
    print(f"Nested power replacement: {check_gate_replacement()} quotient-ring cases.")
