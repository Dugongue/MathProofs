"""Exact finite-field controls for the partition erasure in the written proof."""

from itertools import product
from random import Random


def weight(dimensions, count, index):
    return (count + index + 2) * (dimensions + 1)


def contract(blocks, b, core, markers):
    a = sum(blocks)
    columns = [{row: core[row][col] for row in range(a) if core[row][col]}
               for col in range(b)]
    first_x = 0
    first_private = a
    for index, (width, marker) in enumerate(zip(blocks, markers, strict=True)):
        tag_size = weight(a + b, len(blocks), index)
        if marker:
            columns.extend({first_x + row: marker} for row in range(width))
            for j, col in enumerate(columns[:b]):
                col[first_private + j] = marker
            columns.extend({first_private + b + row: marker} for row in range(tag_size))
        first_x += width
        first_private += b + tag_size
    return columns


def reduce_by_basis(vector, basis, prime):
    remainder = dict(vector)
    while remainder:
        pivot = min(remainder)
        if pivot not in basis:
            break
        coefficient = remainder[pivot]
        for row, entry in basis[pivot].items():
            value = (remainder.get(row, 0) - coefficient * entry) % prime
            if value:
                remainder[row] = value
            else:
                remainder.pop(row, None)
    return remainder


def column_basis(columns, prime):
    basis = {}
    for column in columns:
        reduced = reduce_by_basis(column, basis, prime)
        if reduced:
            pivot = min(reduced)
            inverse = pow(reduced[pivot], -1, prime)
            basis[pivot] = {row: value * inverse % prime for row, value in reduced.items()}
    return basis


def check_small_contractions():
    rng = Random(745)
    checked_ranks = checked_images = 0
    for prime in (2, 3, 5):
        for blocks, b in [((1, 1), 1), ((2, 1), 3), ((1, 2, 1), 2), ((2, 1, 2), 1)]:
            a = sum(blocks)
            k = len(blocks)
            lower = [weight(a + b, k, index) for index in range(k)]
            cores = [[[0] * b for _ in range(a)]]
            cores.extend([[rng.randrange(prime) for _ in range(b)] for _ in range(a)]
                         for _ in range(3))
            for core in cores:
                for markers in product(range(prime), repeat=k):
                    columns = contract(blocks, b, core, markers)
                    basis = column_basis(columns, prime)
                    rank = len(basis)
                    support = tuple(i for i, marker in enumerate(markers) if marker)
                    matching = tuple(i for i, lo in enumerate(lower) if lo <= rank <= lo + a + b)
                    assert (rank <= a + b) == (support == ())
                    assert matching == (support if len(support) == 1 else ())
                    checked_ranks += 1
                    if len(support) == 1:
                        i = support[0]
                        start = sum(blocks[:i])
                        for row in range(start, start + blocks[i]):
                            assert not reduce_by_basis({row: 1}, basis, prime)
                        quotient = [{row: value for row, value in column.items() if row >= a}
                                    for column in columns]
                        quotient_rank = len(column_basis(quotient, prime))
                        assert rank - quotient_rank == blocks[i]
                        checked_images += 1
    return checked_ranks, checked_images


def check_rectangular_widths():
    checked = 0
    for a, b, c in product(range(1, 9), repeat=3):
        for k in range(2, 13):
            dims = a, b, c
            constant = sum(weight(0, k, i) for i in range(k))
            for _ in range(3):
                x, y, z = dims
                pad = (x + y + 1) * constant
                dims = y + x + pad, z + k, x + k * y + pad
            for _ in range(3):
                yp, zp, xp = dims
                total, remainder = divmod(yp - constant, constant + 1)
                assert remainder == 0
                y, remainder = divmod(xp - yp, k - 1)
                assert remainder == 0
                dims = total - y, y, zp - k
            assert dims == (a, b, c)
            checked += 1
    return checked


if __name__ == '__main__':
    ranks, images = check_small_contractions()
    print(f'Passed {ranks} contraction ranks, {images} image intersections, '
          f'and {check_rectangular_widths()} three-stage rectangular width replays.')
