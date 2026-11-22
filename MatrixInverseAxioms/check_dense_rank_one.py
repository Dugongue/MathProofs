"""Check dense nilpotent inputs, low-rank sparsity, and exact single omissions."""

from itertools import product


def zero(n):
    return [[0] * n for _ in range(n)]


def unit(n, i, j):
    result = zero(n)
    result[i][j] = 1
    return result


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def matrix_product(a, b, p):
    return [[sum(x * y for x, y in zip(row, col)) % p
             for col in zip(*b)] for row in a]


def rref(a, p, width):
    rows = [row[:] for row in a]
    pivots = []
    for j in range(width):
        index = len(pivots)
        pivot = next((i for i in range(index, len(rows)) if rows[i][j]), None)
        if pivot is None:
            continue
        pivots.append(j)
        rows[index], rows[pivot] = rows[pivot], rows[index]
        factor = pow(rows[index][j], -1, p)
        rows[index] = [factor * value % p for value in rows[index]]
        for i in range(len(rows)):
            if i != index:
                factor = rows[i][j]
                rows[i] = [(x - factor * y) % p for x, y in zip(rows[i], rows[index])]
    return rows, pivots


def inverse(a, p):
    n = len(a)
    rows, pivots = rref([u + v for u, v in zip(a, eye(n))], p, n)
    assert len(pivots) == n
    return [row[n:] for row in rows]


def square_zero_basis(a, distinguished, p):
    n = len(a)
    _, pivots = rref(a, p, n)
    columns = list(map(list, zip(*a)))
    units = eye(n)
    basis = [columns[j] for j in pivots] + [units[j] for j in pivots] + [distinguished]
    return list(map(list, zip(*basis)))


def check_case(h, p):
    n = 2 * h + 1
    a, sparse = zero(n), zero(n)
    for i, j in product(range(h), repeat=2):
        a[i][h + j] = (int(i == j) + (-1) ** j) % p
    for i in range(h):
        a[h + i][-1] = 1
        sparse[i][h + 1 + i], sparse[i + 1][h + 1 + i] = 1, -1 % p
    ca = [sum(row[h + 1 + i] for i in range(0, h, 2)) % p for row in sparse]
    b_row = [0] * (h + 1) + [i % 2 for i in range(h)]
    b = [[(sparse[i][j] + ca[i] * b_row[j]) % p for j in range(n)] for i in range(n)]
    for j in range(1, h, 2):
        assert sum(b[i][h + 1 + j] != 0 for i in range(n)) >= h - 2
    assert matrix_product(b, b, p) == zero(n)
    t = [1] * h + [0] * (h + 1)
    assert matrix_product(a, a, p) == [[t[i] * int(j == n - 1) for j in range(n)] for i in range(n)]

    # One anchor subtraction removes the single dense row contribution.
    anchor = next(i for i in range(n) if ca[i] != 0)
    for i in range(n):
        factor = ca[i] * pow(ca[anchor], -1, p) % p
        assert [(x - factor * y) % p for x, y in zip(b[i], b[anchor])] == [
            (x - factor * y) % p for x, y in zip(sparse[i], sparse[anchor])]

    total = 0
    for j in range(h, 2 * h):
        c = [row[:] for row in a]
        for i in range(n):
            c[i][j] = (c[i][j] - t[i]) % p
        assert matrix_product(c, c, p) == zero(n)
        source_inverse = inverse(square_zero_basis(c, t, p), p)
        for i in range(h + 1):
            target = square_zero_basis(b, eye(n)[i], p)
            x = matrix_product(target, source_inverse, p)
            y = inverse(x, p)
            assert matrix_product(x, y, p) == eye(n) == matrix_product(y, x, p)
            xa, bx = matrix_product(x, a, p), matrix_product(b, x, p)
            assert [[(u - v) % p for u, v in zip(row, col)]
                    for row, col in zip(xa, bx)] == unit(n, i, j)
            total += 1
    return total


if __name__ == "__main__":
    primes = (2, 3, 5, 7)
    sizes = (2, 4, 6, 8)
    witnesses = sum(check_case(h, p) for h in sizes for p in primes)
    print(f"Verified {witnesses} invertible single-omission witnesses for {len(primes) * len(sizes)} dense input pairs.")
