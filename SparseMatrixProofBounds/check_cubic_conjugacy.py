"""Direct finite-field witnesses for the two cubic conjugacy families."""

from itertools import product


def zero(n):
    return [[0] * n for _ in range(n)]


def eye(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def transpose(a):
    return [list(column) for column in zip(*a)]


def multiply(a, b, p):
    return [[sum(x * y for x, y in zip(row, col)) % p
             for col in zip(*b)] for row in a]


def add(a, b, p, sign=1):
    return [[(x + sign * y) % p for x, y in zip(row, other)]
            for row, other in zip(a, b)]


def reduce_rows(a, p, stop=None):
    a = [row[:] for row in a]
    columns = range(len(a[0]) if stop is None else stop)
    pivots = []
    for j in columns:
        row = len(pivots)
        pivot = next((i for i in range(row, len(a)) if a[i][j]), None)
        if pivot is None:
            continue
        a[row], a[pivot] = a[pivot], a[row]
        scale = pow(a[row][j], -1, p)
        a[row] = [x * scale % p for x in a[row]]
        for i in range(len(a)):
            if i != row and a[i][j]:
                factor = a[i][j]
                a[i] = [(x - factor * y) % p for x, y in zip(a[i], a[row])]
        pivots.append(j)
    return a, pivots


def inverse(a, p):
    n = len(a)
    rows, pivots = reduce_rows([r + s for r, s in zip(a, eye(n))], p, n)
    assert len(pivots) == n
    return [row[n:] for row in rows]


def unit(n, i, j):
    a = zero(n)
    a[i][j] = 1
    return a


def square_zero_basis(a, distinguished, p):
    columns, units = transpose(a), eye(len(a))
    _, pivots = reduce_rows(a, p)
    return transpose([columns[j] for j in pivots]
                     + [units[j] for j in pivots] + [distinguished])


def nilpotent_checks(h, p):
    n = 2 * h + 1
    a, b = zero(n), zero(n)
    for i, j in product(range(h), repeat=2):
        a[i][h+j] = (int(i == j) + (-1)**j) % p
    for i in range(h):
        a[h+i][-1] = 1
        b[i][h+1+i], b[i+1][h+1+i] = 1, -1 % p
    t = [1] * h + [0] * (h+1)
    tlast = zero(n)
    for i in range(h):
        tlast[i][-1] = 1
    assert multiply(a, a, p) == tlast
    assert multiply(b, b, p) == zero(n)
    total = 0
    for j in range(h, 2*h):
        c = [row[:] for row in a]
        for i, y in enumerate(t):
            c[i][j] = (c[i][j] - y) % p
        assert multiply(c, c, p) == zero(n)
        source_inverse = inverse(square_zero_basis(c, t, p), p)
        for i in range(h+1):
            target = square_zero_basis(b, eye(n)[i], p)
            x = multiply(target, source_inverse, p)
            assert multiply(x, inverse(x, p), p) == eye(n)
            assert add(multiply(x, a, p), multiply(b, x, p), p, -1) == unit(n, i, j)
            total += 1
    return total


def coprime_checks(n, p):
    j, b = zero(n), zero(n)
    for k in range(n-1):
        j[k][k+1] = 1
    for k in range(n):
        b[(k+1) % n][k] = 1
    u = [0] + [1] * (n-1)
    v = [0 if k % 2 else (-1)**(k//2) for k in range(n)]
    shear = [[(int(i == j0) + u[i]*v[j0]) % p for j0 in range(n)] for i in range(n)]
    a = multiply(multiply(shear, j, p), inverse(shear, p), p)
    a_powers = [eye(n)]
    b_inv = inverse(b, p)
    b_inv_powers = [b_inv]
    for _ in range(1, n):
        a_powers.append(multiply(a_powers[-1], a, p))
        b_inv_powers.append(multiply(b_inv_powers[-1], b_inv, p))
    for i, j0 in product(range(n), repeat=2):
        x = zero(n)
        for left, right in zip(b_inv_powers, a_powers):
            for row, col in product(range(n), repeat=2):
                x[row][col] = (x[row][col] - left[row][i] * right[j0][col]) % p
        assert add(multiply(x, a, p), multiply(b, x, p), p, -1) == unit(n, i, j0)
        assert multiply(x, inverse(x, p), p) == eye(n)
    return n*n


def binary_exhaustive():
    matrices = [[list(items[:2]), list(items[2:])] for items in product(range(2), repeat=4)]
    invertibles = [a for a in matrices if len(reduce_rows(a, 2)[1]) == 2]
    total = 0
    for a, b in product(matrices, repeat=2):
        errors = [add(multiply(x, a, 2), multiply(b, x, 2), 2) for x in invertibles]
        if zero(2) in errors:
            continue
        observed = all(unit(2, i, j) in errors for i, j in product(range(2), repeat=2))
        images = []
        for i, j in product(range(2), repeat=2):
            e = unit(2, i, j)
            h = add(multiply(e, a, 2), multiply(b, e, 2), 2)
            images.append(h[0] + h[1])
        coprime = len(reduce_rows(images, 2)[1]) == 4
        cyclic = all(a[j][1-j] and b[1-j][j] for j in range(2))
        assert observed == (coprime and cyclic)
        total += 1
    return total


if __name__ == "__main__":
    print("Isospectral single-omission witnesses:",
          sum(nilpotent_checks(h, p) for p in (2, 3, 5, 7) for h in (2, 4, 6)))
    print("Coprime single-omission witnesses:",
          sum(coprime_checks(n, p) for p in (2, 3, 5, 7) for n in (5, 9)))
    print("Nonconjugate binary side-two pairs:", binary_exhaustive())
