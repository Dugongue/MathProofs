"""Exact finite checks for determinant-preserving castling and split volumes."""

from itertools import combinations, permutations, product
from random import Random


MODULUS = 3


def sign(permutation):
    return (-1) ** sum(
        left > right
        for i, left in enumerate(permutation)
        for right in permutation[i + 1 :]
    )


def det(matrix):
    order = len(matrix)
    total = 0
    for permutation in permutations(range(order)):
        term = sign(permutation)
        for row, column in enumerate(permutation):
            term *= matrix[row][column]
        total += term
    return total % MODULUS


def transpose(matrix):
    return tuple(zip(*matrix))


def multiply(left, right):
    return tuple(
        tuple(sum(a * b for a, b in zip(row, column)) % MODULUS
              for column in transpose(right))
        for row in left
    )


def kronecker(left, right):
    return tuple(
        tuple(a * b % MODULUS for a in first for b in second)
        for first in left for second in right
    )


def complement_covector(columns):
    height = len(columns)
    assert len(columns[0]) == height - 1
    return tuple(
        (-1) ** (j + height - 1)
        * det(tuple(row for i, row in enumerate(columns) if i != j)) % MODULUS
        for j in range(height)
    )


def check_castling():
    columns = ((1, 0, 1), (0, 1, 2), (0, 0, 1), (1, 1, 0))
    source = complement_covector(columns)
    gl2 = []
    for a, b, c, d in product(range(MODULUS), repeat=4):
        matrix = ((a, b), (c, d))
        if det(matrix):
            gl2.append(matrix)

    total = 0
    for left, right in product(gl2, repeat=2):
        ambient = kronecker(left, right)
        for pivot in (1, 2):
            first_axis = ((pivot, 0, 0), (0, 1, 0), (0, 0, 1))
            changed = multiply(multiply(ambient, columns), transpose(first_axis))
            target = complement_covector(changed)
            expected_factor = (pivot * det(left)**2 * det(right)**2) % MODULUS
            # Evaluate the castling formula at the transformed ambient basis.
            pullback = multiply((target,), ambient)[0]
            assert pullback == tuple(expected_factor * value % MODULUS for value in source)
            total += 1
    assert total == 4608
    return total


def check_split_volume():
    rng = Random(17)
    checked = 0
    while checked < 64:
        matrix = tuple(tuple(rng.randrange(MODULUS) for _ in range(4)) for _ in range(4))
        determinant = det(matrix)
        if not determinant:
            continue
        # Use E_1, E_1, E_2 on the three modes.
        exterior_pair = {
            indices: det(tuple(tuple(matrix[i][j] for j in (2, 3)) for i in indices))
            for indices in combinations(range(4), 2)
        }
        volume = 0
        for (a, b), value in exterior_pair.items():
            for i, j in permutations(set(range(4)) - {a, b}):
                volume += sign((i, j, a, b)) * matrix[i][0] * matrix[j][1] * value
        assert volume % MODULUS == determinant
        checked += 1
    return checked


print(f"Checked {check_castling()} castling determinant identities and "
      f"{check_split_volume()} split-volume identities over F3.")
