from collections import Counter
from itertools import product


ROWS = 4
COLS = 3


def rank(matrix):
    rows = [(matrix >> (i * COLS)) & ((1 << COLS) - 1) for i in range(ROWS)]
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def encode(rows):
    return sum(value << (i * COLS) for i, value in enumerate(rows))


def outer(x, y):
    return encode([y if x & (1 << i) else 0 for i in range(ROWS)])


def dual_ranks(generators):
    return Counter(rank(matrix) for matrix in range(1 << (ROWS * COLS))
                   if all((matrix & g).bit_count() % 2 == 0 for g in generators))


def kernel(a, b):
    return {0, a, b, a ^ b}


def left_support(a, b):
    vectors = set()
    for generator in (a, b):
        for j in range(COLS):
            vectors.add(sum(((generator >> (i * COLS + j)) & 1) << i
                            for i in range(ROWS)))
    space = {0}
    for vector in vectors:
        space |= {vector ^ v for v in space}
    return len(space).bit_length() - 1


def main():
    eye = encode([1, 2, 4, 0])
    field_shift = encode([4, 5, 2, 0])
    row_shift = encode([0, 1, 2, 4])
    k1 = kernel(eye, field_shift)
    k2 = kernel(eye, row_shift)
    assert {rank(k) for k in k1 - {0}} == {3}
    assert {rank(k) for k in k2 - {0}} == {3}
    assert [left_support(eye, a) for a in (field_shift, row_shift)] == [3, 4]
    dual = dual_ranks((eye, field_shift))
    assert dual == dual_ranks((eye, row_shift))
    pairs = tuple(product(range(1 << ROWS), range(1 << COLS)))
    for x, y in pairs:
        matches = 0
        for a, b in pairs:
            difference = outer(x, b) ^ outer(a, y)
            assert (difference in k1) == (difference in k2) == (difference == 0)
            matches += difference == 0
        assert matches == (len(pairs) if x == y == 0 else
                           1 << ROWS if y == 0 else 1 << COLS if x == 0 else 2)
    degrees = {1 << j: count * (1 << (ROWS + COLS - 2 * j))
               for j, count in sorted(dual.items())}
    print("Different support dimensions, identical commuting relations.")
    print("Dual rank distribution:", dict(sorted(dual.items())))
    print("Common character-degree multiplicities:", degrees)


if __name__ == "__main__":
    main()
