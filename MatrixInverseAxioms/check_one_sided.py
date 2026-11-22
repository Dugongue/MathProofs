from itertools import product
from random import Random


def identity(side):
    return [[int(i == j) for j in range(side)] for i in range(side)]


def transpose(matrix):
    return [list(column) for column in zip(*matrix)]


def multiply(left, right, prime):
    return [[sum(a * b for a, b in zip(row, column)) % prime
             for column in zip(*right)] for row in left]


def subtract(left, right, prime):
    return [[(a - b) % prime for a, b in zip(row_a, row_b)]
            for row_a, row_b in zip(left, right)]


def diagonal_blocks(*blocks):
    height = sum(len(block) for block in blocks)
    width = sum(len(block[0]) for block in blocks)
    matrix = [[0] * width for _ in range(height)]
    row_offset = 0
    col_offset = 0
    for block in blocks:
        for i, row in enumerate(block):
            matrix[row_offset + i][col_offset:col_offset + len(row)] = row
        row_offset += len(block)
        col_offset += len(block[0])
    return matrix


def projection(side, rank):
    return [[int(i == j < rank) for j in range(side)] for i in range(side)]


def hyperbolic(planes, prime):
    return [[(int(j == i + planes) - int(i == j + planes)) % prime
             for j in range(2 * planes)] for i in range(2 * planes)]


def random_matrix(height, width, prime, generator):
    return [[generator.randrange(prime) for _ in range(width)]
            for _ in range(height)]


def check_square_identities(x, y, prime):
    dim = len(x)
    source = projection(dim, dim - 1)
    target = identity(dim)
    gram = subtract(multiply(multiply(x, source, prime), transpose(x), prime),
                    target, prime)
    residual = subtract(identity(dim), multiply(y, x, prime), prime)
    expected = subtract(multiply(x, source, prime),
                        multiply(target, transpose(y), prime), prime)
    actual = subtract(multiply(gram, transpose(y), prime),
                      multiply(multiply(x, source, prime),
                               transpose(subtract(multiply(y, x, prime),
                                                  identity(dim), prime)), prime), prime)
    assert actual == expected
    assert multiply(x, residual, prime) == multiply(
        subtract(identity(dim), multiply(x, y, prime), prime), x, prime)


def check_rectangular_specializations(p, q, prime):
    s, r = len(p), len(p[0])
    side = s + r
    u = [row + [0] * (s - r) for row in identity(r)]
    conj_x = diagonal_blocks(p, u)
    conj_y = diagonal_blocks(q, transpose(u))
    source = projection(side, r)
    target = projection(side, s)
    assert multiply(conj_x, source, prime) == multiply(target, conj_x, prime)
    independent = multiply(p, q, prime)
    assert multiply(conj_x, conj_y, prime) == diagonal_blocks(independent, identity(r))
    gram_y = diagonal_blocks(transpose(p), transpose(u))
    symmetric = multiply(p, transpose(p), prime)
    assert multiply(conj_x, gram_y, prime) == diagonal_blocks(symmetric, identity(r))
    assert multiply(multiply(conj_x, source, prime),
                    transpose(conj_x), prime) == diagonal_blocks(
                        symmetric, [[0] * r for _ in range(r)])
    alt_x = diagonal_blocks(p, transpose(q))
    skew = multiply(multiply(alt_x, hyperbolic(r, prime), prime),
                    transpose(alt_x), prime)
    for i in range(s):
        for j in range(s):
            assert skew[i][j] == skew[s + i][s + j] == 0
            assert skew[i][s + j] == independent[i][j]
            assert skew[s + j][i] == -independent[i][j] % prime
    off_x = diagonal_blocks(p, [[1, 1]])
    off_y = diagonal_blocks(q, [[1], [0]])
    assert multiply(off_x, off_y, prime) == diagonal_blocks(independent, [[1]])
    assert multiply(off_y, off_x, prime)[r][r + 1] == 1


generator = Random(20261121)
square_cases = 0
for prime in (2, 3):
    for entries in product(range(prime), repeat=8):
        check_square_identities([list(entries[:2]), list(entries[2:4])],
                                [list(entries[4:6]), list(entries[6:])], prime)
        square_cases += 1

rectangular_cases = 0
for prime in (2, 3, 5, 7):
    for r in range(1, 5):
        for s in range(r + 1, 2 * r + 2):
            for _ in range(20):
                check_rectangular_specializations(
                    random_matrix(s, r, prime, generator),
                    random_matrix(r, s, prime, generator), prime)
                rectangular_cases += 1

print(f"Checked {square_cases} square identities and {rectangular_cases} rectangular specializations.")
