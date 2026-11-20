"""Finite checks for the promised abelian-group DNF lower bound."""

from itertools import product
from math import prod


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pivot = row.bit_length()
            if pivot in pivots:
                row ^= pivots[pivot]
            else:
                pivots[pivot] = row
                break
    return len(pivots)


def multiply_by_vector(matrix, vector):
    return sum(((row & vector).bit_count() % 2) << i
               for i, row in enumerate(matrix))


def cayley_product(matrix, first, second):
    left, left_central = first
    right, right_central = second
    return (
        left ^ right,
        left_central ^ right_central ^ multiply_by_vector(matrix, left & right),
    )


def check_tables(dimension):
    vectors = range(1 << dimension)
    elements = list(product(vectors, repeat=2))
    identity = (0, 0)
    for matrix in product(vectors, repeat=dimension):
        squares = {cayley_product(matrix, element, element) for element in elements}
        assert len(squares) == 1 << binary_rank(matrix)
        assert all(cayley_product(matrix, square, square) == identity for square in squares)
        assert all(cayley_product(matrix, element, identity) == element for element in elements)
        assert all(cayley_product(matrix, a, b) == cayley_product(matrix, b, a)
                   for a, b in product(elements, repeat=2))
        if dimension <= 2:
            assert all(
                cayley_product(matrix, cayley_product(matrix, a, b), c)
                == cayley_product(matrix, a, cayley_product(matrix, b, c))
                for a, b, c in product(elements, repeat=3)
            )


def affine_row_sets(dimension):
    vectors = range(1 << dimension)
    subspaces = {frozenset({0})}
    for vector in vectors:
        subspaces |= {space | {point ^ vector for point in space} for space in subspaces}
    return {
        frozenset(point ^ translate for point in space)
        for space in subspaces for translate in vectors
    }


def check_every_row_product(dimension, invertibles):
    affine_sets = affine_row_sets(dimension)
    largest = max(
        prod(map(len, row_sets))
        for row_sets in product(affine_sets, repeat=dimension)
        if all(matrix in invertibles for matrix in product(*row_sets))
    )
    assert largest == 1 << (dimension * (dimension - 1) // 2)
    return largest


def row_times_matrix(row, matrix):
    combined = 0
    for i, basis_image in enumerate(matrix):
        if row >> i & 1:
            combined ^= basis_image
    return combined


def check_coset_partition(dimension, invertibles):
    triangular_row_sets = [
        tuple((1 << i) | (tail << (i + 1))
              for tail in range(1 << (dimension - i - 1)))
        for i in range(dimension)
    ]
    remaining = set(invertibles)
    count = 0
    while remaining:
        representative = next(iter(remaining))
        translated_rows = [
            {row_times_matrix(row, representative) for row in row_set}
            for row_set in triangular_row_sets
        ]
        coset = set(product(*translated_rows))
        assert coset <= remaining
        assert len(coset) == 1 << (dimension * (dimension - 1) // 2)
        remaining -= coset
        count += 1
    expected = prod((1 << j) - 1 for j in range(1, dimension + 1))
    assert count == expected
    return count


def main():
    for dimension in range(1, 5):
        vectors = range(1 << dimension)
        invertibles = {
            matrix for matrix in product(vectors, repeat=dimension)
            if binary_rank(matrix) == dimension
        }
        count = check_coset_partition(dimension, invertibles)
        if dimension <= 3:
            check_tables(dimension)
            largest = check_every_row_product(dimension, invertibles)
            print(f"k={dimension}, invertible={len(invertibles)}, "
                  f"max row product={largest}, exact terms={count}")
        else:
            print(f"k={dimension}, invertible={len(invertibles)}, coset count={count}")


if __name__ == "__main__":
    main()
