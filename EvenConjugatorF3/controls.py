"""Exact deterministic orientation checks over F3. Run with Python 3."""

from itertools import combinations_with_replacement, product


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def det(matrix):
    a = [[v % 3 for v in row] for row in matrix]
    value = 1
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return 0
        if pivot != j:
            a[j], a[pivot] = a[pivot], a[j]
            value = -value
        t = a[j][j]
        value = value * t % 3
        for i in range(j + 1, len(a)):
            k = a[i][j] * t % 3  # t = t^{-1} over F3.
            if k:
                for c in range(j, len(a)):
                    a[i][c] = (a[i][c] - k * a[j][c]) % 3
    return value % 3


def block(a, indices):
    return [[a[i][j] for j in indices] for i in indices]


def restricts(a, indices):
    return all(not a[i][j] for i in range(len(a)) if i not in indices
               for j in indices)


def sym_square(g):
    pairs = list(combinations_with_replacement(range(len(g)), 2))
    return [[(g[i][a] * g[j][b] + (i != j) * g[j][a] * g[i][b]) % 3
             for a, b in pairs] for i, j in pairs]


def parabolic_generators(n, b):
    # The first b coordinates are the named subspace.
    for i in range(n):
        g = identity(n)
        g[i][i] = 2
        yield g
        for j in range(n):
            if j != i and (i < b or j >= b):
                g = identity(n)
                g[i][j] = 1
                yield g


def sign_data(g, relations):
    s = sym_square(g)
    assert restricts(s, relations)
    z = [i for i in range(len(s)) if i not in relations]
    total = det(g) * det(block(s, z)) % 3
    assert total == det(block(s, relations))
    return s, total


def run():
    pairs = list(combinations_with_replacement(range(6), 2))
    envelope = [i for i, (_, j) in enumerate(pairs) if j < 3]
    checks = 0
    for g in parabolic_generators(6, 3):
        s, sign = sign_data(g, envelope)
        z = [i for i in range(len(s)) if i not in envelope]
        h = block(s, z)
        # D beta changes the first output coordinate by a nonsquare.
        h[0] = [(-v) % 3 for v in h[0]]
        assert sign == 1 and det(g) * det(h) % 3 == 2
        checks += 2

    # A second split (6,17) example with odd support and two-dimensional defect.
    relations = [i for i in envelope
                 if pairs[i][0] == pairs[i][1] or pairs[i] == (0, 1)]
    q = [i for i in envelope if i not in relations]
    small_pairs = list(combinations_with_replacement(range(3), 2))
    small_rel = [i for i, (j, k) in enumerate(small_pairs)
                 if j == k or (j, k) == (0, 1)]
    signs = {1: 0, 2: 0}
    all_gl3 = 0
    for entries in product(range(3), repeat=9):
        h = [entries[i:i + 3] for i in (0, 3, 6)]
        if not det(h):
            continue
        all_gl3 += 1
        if not restricts(sym_square(h), small_rel):
            continue
        g = identity(6)
        for i in range(3):
            g[i][:3] = h[i]
        s, sign = sign_data(g, relations)
        assert sign == det(block(s, q))
        signs[sign] += 1
    assert all_gl3 == 11232 and all(signs.values())

    # Partial carrier U X, U the first three coordinates of X of dimension 4.
    # Sym^2(span(e0,e1)) is the common kernel. The omitted e3^2 is the cokernel.
    p4 = list(combinations_with_replacement(range(4), 2))
    partial = [i for i, (j, _) in enumerate(p4) if j < 3]
    rel4 = [i for i, (_, k) in enumerate(p4) if k < 2]
    kernel = [i for i in partial if i in rel4]
    cokernel = [i for i in range(len(p4)) if i not in rel4 and i not in partial]
    partial_checks = 0
    for g in parabolic_generators(4, 2):
        if not restricts(g, range(3)):
            continue
        s, sign = sign_data(g, rel4)
        assert restricts(s, partial)
        assert sign == det(block(s, kernel)) * det(block(s, cokernel)) % 3
        partial_checks += 1
    print(f"Split (6,15) parabolic generator and output-twist checks: {checks}")
    print(f"Enumerated GL(3,3): {all_gl3}; preserving (6,17) support tests: "
          f"{sum(signs.values())} (positive {signs[1]}, negative {signs[2]})")
    print(f"Partial-carrier checks: {partial_checks}")
    print(f"Total sign checks passed: {checks + sum(signs.values()) + partial_checks}")


if __name__ == "__main__":
    run()
