"""Exact finite controls for the two-copy isolator and marked width."""

from itertools import combinations, product


def coefficient_basis(columns, p):
    pivots = {}
    for col in columns:
        col = {key: value % p for key, value in col.items() if value % p}
        while col:
            leading = min(col)
            value = col[leading]
            if leading not in pivots:
                inv = pow(value, -1, p)
                pivots[leading] = {key: entry * inv % p for key, entry in col.items()}
                break
            for key, entry in pivots[leading].items():
                new = (col.get(key, 0) - value * entry) % p
                if new:
                    col[key] = new
                else:
                    col.pop(key, None)
    return len(pivots)


def path_matrix(r, p):
    s = [[0] * (2 * r) for _ in range(2 * r)]
    for i in range(r):
        s[i][r + i] = 1
        s[r + i][i] = -1 % p
    for start in (0, 1):
        offset = start * r
        for i in range(start, r - 1, 2):
            s[offset + i][offset + i + 1] = 1
            s[offset + i + 1][offset + i] = -1 % p
    return s


def quotient_columns(d, m, r, p):
    s = path_matrix(r, p)
    assert coefficient_basis((dict(enumerate(row)) for row in s), p) == 2 * r
    columns = []
    for row, col in product(range(d), range(2 * d)):
        coeff = {}
        for j in range(m):
            y = (1, j, col)
            if row >= r:
                x_values = [((0, j, row), 1)]
            elif j < 2:
                x_values = [
                    ((1, k // r, k % r), -entry)
                    for k, entry in enumerate(s[j * r + row])
                ]
            else:
                x_values = []
            for x, value in x_values:
                key = tuple(sorted((x, y)))
                coeff[key] = (coeff.get(key, 0) + value) % p
        columns.append(coeff)
    return columns


def restrict(matrix, columns, p):
    coeffs = {}
    for a, column in zip((x for row in matrix for x in row), columns):
        for key, entry in column.items():
            coeffs[key] = (coeffs.get(key, 0) + a * entry) % p
    return coeffs


def normal_form(b, others, p):
    matrices = [[list(row) for row in a] for a in (b, *others)]
    d, e = len(b), len(b[0])
    r = 0
    while r < min(d, e):
        candidates = ((i, j) for i, j in product(range(r, d), range(r, e))
                      if matrices[0][i][j] % p)
        pivot = next(candidates, None)
        if pivot is None:
            break
        i, j = pivot
        for a in matrices:
            a[i], a[r] = a[r], a[i]
            for row in a:
                row[j], row[r] = row[r], row[j]
        inv = pow(matrices[0][r][r], -1, p)
        for a in matrices:
            a[r] = [v * inv % p for v in a[r]]
        for i in range(d):
            if i == r:
                continue
            factor = matrices[0][i][r]
            for a in matrices:
                a[i] = [(x - factor * y) % p for x, y in zip(a[i], a[r])]
        for j in range(e):
            if j == r:
                continue
            factor = matrices[0][r][j]
            for a in matrices:
                for row in a:
                    row[j] = (row[j] - factor * row[r]) % p
        r += 1
    assert matrices[0] == [[int(i == j and i < r) for j in range(e)] for i in range(d)]
    return r, matrices[1:]


def anchored(data):
    d = 4
    a = [[0] * (2 * d) for _ in range(d)]
    for i, j in product(range(2), repeat=2):
        a[2 + i][j] = data[i][j]
    return a


def threshold_control():
    d, p, m = 4, 2, 2
    i0 = [[int(i == j) for j in range(2 * d)] for i in range(d)]
    i1 = [[int(i + d == j) for j in range(2 * d)] for i in range(d)]
    a = anchored(((1, 0), (0, 0)))
    b = anchored(((0, 1), (1, 0)))
    c = [[(x + y) % p for x, y in zip(ax, bx)] for ax, bx in zip(a, b)]
    differences = []
    for digits in product(range(2), repeat=4):
        if not any(digits):
            continue
        target = anchored((digits[:2], digits[2:]))
        r, full = normal_form(target, (i0, i1, a, b), p)
        columns = quotient_columns(d, m, r, p)
        forms = [restrict(x, columns, p) for x in full]
        large_kernel = len(forms) - coefficient_basis(forms, p)
        small_kernel = len(forms) - 1 - coefficient_basis(forms[:-1], p)
        assert large_kernel == int(target in (a, b, c))
        assert small_kernel == int(target == a)
        if large_kernel != small_kernel:
            differences.append(m * r)
    assert differences == [4, 4]
    print("F_2: all 15 nonzero 2-by-2 membership probes passed, first discordance at width 4")


def mul7(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a & 128:
            a ^= 131  # X^7 + X + 1
        b >>= 1
    return result


def field_orbits():
    current = 1
    powers = set()
    for _ in range(127):
        powers.add(current)
        current = mul7(current, 2)
    assert current == 1 and len(powers) == 127
    spaces = set()
    for a, b, c in combinations(range(1, 128), 3):
        if a ^ b == c:
            continue
        spaces.add(tuple(sorted((a, b, c, a ^ b, a ^ c, b ^ c, a ^ b ^ c))))
    assert len(spaces) == 11811
    orbits = 0
    while spaces:
        first = spaces.pop()
        stack = [first]
        while stack:
            space = stack.pop()
            moves = [
                tuple(sorted(mul7(x, 2) for x in space)),
                tuple(sorted(mul7(x, x) for x in space)),
            ]
            for neighbor in moves:
                if neighbor in spaces:
                    spaces.remove(neighbor)
                    stack.append(neighbor)
        orbits += 1
    assert orbits >= 14
    print(f"F_2: 11,811 three-spaces in F_128 give {orbits} scalar-Frobenius orbits")


if __name__ == "__main__":
    checks = 0
    for p, m, r in product((2, 3, 5), (2, 3), range(1, 7)):
        d = r + 1
        columns = quotient_columns(d, m, r, p)
        assert coefficient_basis(columns, p) == 2 * d * d - 1
        checks += 1
    print(f"{checks} exact quotient kernel dimensions verified")
    threshold_control()
    field_orbits()
