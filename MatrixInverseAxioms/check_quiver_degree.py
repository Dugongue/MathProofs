"""Cross-check degree two in the original quiver encoding and center ranks."""

from itertools import product
from random import Random


def rref(rows, width, p):
    work = [[x % p for x in row] for row in rows]
    pivots = []
    for col in range(width):
        k = len(pivots)
        position = next((i for i in range(k, len(work)) if work[i][col]), None)
        if position is None:
            continue
        work[k], work[position] = work[position], work[k]
        inverse = pow(work[k][col], -1, p)
        work[k] = [(c * inverse) % p for c in work[k]]
        for i in range(len(work)):
            scalar = work[i][col]
            if i != k and scalar:
                work[i] = [(a - scalar * b) % p for a, b in zip(work[i], work[k])]
        pivots.append(col)
    return work[:len(pivots)], pivots


def kernel(rows, width, p):
    reduced, pivots = rref(rows, width, p)
    basis = []
    for free in range(width):
        if free in pivots:
            continue
        vector = [0] * width
        vector[free] = 1
        for row, j in zip(reduced, pivots):
            vector[j] = -row[free] % p
        basis.append(vector)
    return basis


def coordinates(a, b):
    return [(v, i, j) for v in range(len(a)) for i in range(b[v]) for j in range(a[v])]


def add_to(row, column, value):
    row[column] = row.get(column, 0) + value


def linear_inputs(a, b, arrows):
    equations = []
    for s, t, ma, mb in arrows:
        for i, j in product(range(b[t]), range(a[s])):
            coeffs = {}
            for k in range(a[t]):
                add_to(coeffs, (t, i, k), ma[k][j])
            for k in range(b[s]):
                add_to(coeffs, (s, k, j), -mb[i][k])
            equations.append(coeffs)
    return equations


def direct_quadratic_test(a, b, arrows, p):
    xvars = coordinates(a, b)
    yvars = coordinates(b, a)
    echelon = {}

    def insert(row):
        row = {key: value % p for key, value in row.items() if value % p}
        while row:
            pivot = min(row)
            old = echelon.get(pivot)
            scalar = row[pivot]
            if old is None:
                scalar = pow(scalar, -1, p)
                echelon[pivot] = {key: (value * scalar) % p for key, value in row.items()}
                return
            for key, value in old.items():
                c = (row.get(key, 0) - value * scalar) % p
                if c:
                    row[key] = c
                else:
                    row.pop(key, None)

    constant = (1,)
    for equation in linear_inputs(a, b, arrows):
        for y in yvars:
            insert({(0, x, y): c for x, c in equation.items()})
    for v in range(len(a)):
        for i, j in product(range(a[v]), repeat=2):
            row = {(0, (v, k, j), (v, i, k)): 1 for k in range(b[v])}
            if i == j:
                row[constant] = -1
            insert(row)
        for i, j in product(range(b[v]), repeat=2):
            row = {(0, (v, i, k), (v, k, j)): 1 for k in range(a[v])}
            if i == j:
                row[constant] = -1
            insert(row)
    return constant in echelon


def trace_test(a, b, arrows, p):
    xvars = coordinates(a, b)
    idx = {x: i for i, x in enumerate(xvars)}
    equations = [[line.get(x, 0) for x in xvars] for line in linear_inputs(a, b, arrows)]
    hom = kernel(equations, len(xvars), p)
    for v, (n, m) in enumerate(zip(a, b)):
        width = n*n + m*m
        pair_eqs = []
        for x in hom:
            for i, j in product(range(m), range(n)):
                row = [0] * width
                for k in range(n):
                    row[k*n+j] = x[idx[v, i, k]]
                for k in range(m):
                    row[n*n+i*m+k] = -x[idx[v, k, j]]
                pair_eqs.append(row)
        if any(
            (sum(w[i*n+i] for i in range(n))
             - sum(w[n*n+j*m+j] for j in range(m))) % p
            for w in kernel(pair_eqs, width, p)
        ):
            return True
    return False


def random_checks():
    rng = Random(108237)
    checked = 0
    for p in (2, 3, 5):
        for _ in range(100):
            vertices = rng.randint(1, 3)
            a = [rng.randrange(3) for _ in range(vertices)]
            b = [rng.randrange(3) for _ in range(vertices)]
            arrows = []
            for _ in range(rng.randint(0, 4)):
                s, t = rng.choices(range(vertices), k=2)
                ma = [[rng.randrange(p) for _ in range(a[s])] for _ in range(a[t])]
                mb = [[rng.randrange(p) for _ in range(b[s])] for _ in range(b[t])]
                arrows.append((s, t, ma, mb))
            assert direct_quadratic_test(a, b, arrows, p) == trace_test(a, b, arrows, p)
            checked += 1
    return checked


def rank_normal(shape, rank):
    m, n = shape
    return [[int(i == j and i < rank) for j in range(n)] for i in range(m)]


def one_arrow_checks():
    checked = 0
    for p in (2, 3, 5):
        for m, n in product(range(1, 6), repeat=2):
            for r, s in product(range(min(m, n) + 1), repeat=2):
                if r == s:
                    continue
                arrows = [(0, 1, rank_normal((n, m), r), rank_normal((n, m), s))]
                expected = min(r, s) == 0 or s == m or r == n
                assert direct_quadratic_test([m, n], [m, n], arrows, p) == expected, (p, m, n, r, s)
                checked += 1
    return checked


def mul_binary(a, b, modulus):
    degree = modulus.bit_length() - 1
    result = 0
    while b:
        if b & 1:
            result ^= a
        a <<= 1
        if a >> degree:
            a ^= modulus
        b >>= 1
    return result


def center_profiles(moduli, widths, ranks):
    """Use only the multiplication and action tables of the center."""
    degrees = [polynomial.bit_length() - 1 for polynomial in moduli]
    center_offsets = [sum(degrees[:i]) for i in range(len(degrees))]
    module_offsets = [sum(w*d for w, d in zip(widths[:i], degrees[:i])) for i in range(len(degrees))]
    cd = sum(degrees)
    md = sum(w*d for w, d in zip(widths, degrees))

    def unpack(v, off, d):
        return sum(v[off+j] << j for j in range(d))

    def update(out, start, d, a):
        for j in range(d):
            out[start+j] = (a >> j) & 1

    def cmul(v, w):
        out = [0]*cd
        for off, d, f in zip(center_offsets, degrees, moduli):
            update(out, off, d, mul_binary(unpack(v, off, d), unpack(w, off, d), f))
        return out

    def act(v, w):
        out = [0]*md
        for c, m, d, f, width in zip(center_offsets, module_offsets, degrees, moduli, widths):
            a = unpack(v, c, d)
            for j in range(width):
                off = m + j*d
                update(out, off, d, mul_binary(a, unpack(w, off, d), f))
        return out

    def standard(dimension):
        return [[int(i == j) for i in range(dimension)] for j in range(dimension)]

    def combine(coefs, vectors):
        return [sum(c*v for c, v in zip(coefs, col)) % 2 for col in zip(*vectors)]

    def solve(basis, value):
        equations = [list(col) + [b] for col, b in zip(zip(*basis), value)]
        reduced, pivots = rref(equations, len(basis)+1, 2)
        assert pivots == list(range(len(basis)))
        return [row[-1] for row in reduced]

    sectors = []

    def split(center_basis, identity, module_basis, count):
        if not module_basis:
            sectors.append((identity, count))
            return
        x = module_basis[0]
        images = [act(c, x) for c in center_basis]
        icoefs = kernel(list(zip(*images)), len(center_basis), 2)
        ibasis = [combine(i, center_basis) for i in icoefs]
        equations = [coord for i in ibasis for coord in zip(*(cmul(i, c) for c in center_basis))]
        jbasis = [combine(j, center_basis) for j in kernel(equations, len(center_basis), 2)]
        ordered = ibasis + jbasis
        coefs = solve(ordered, identity)
        if ibasis:
            e = combine(coefs[:len(ibasis)], ibasis)
            vbasis, _ = rref([act(e, v) for v in module_basis], md, 2)
            split(ibasis, e, vbasis, count)
        if jbasis:
            e = combine(coefs[len(ibasis):], jbasis)
            orbit = [act(c, x) for c in jbasis]
            reduced, pivots = rref(orbit, md, 2)
            remainders = []
            for v in module_basis:
                w = act(e, v)
                for pivot, row in zip(pivots, reduced):
                    if w[pivot]:
                        w = [a ^ b for a, b in zip(w, row)]
                remainders.append(w)
            vbasis, _ = rref(remainders, md, 2)
            split(jbasis, e, vbasis, count + 1)

    identity = [int(i in center_offsets) for i in range(cd)]
    vectors = standard(md)
    rng = Random(9811)
    for i in range(5*md):
        a, b = rng.sample(range(md), 2)
        vectors[a] = [x ^ y for x, y in zip(vectors[a], vectors[b])]
    rng.shuffle(vectors)
    split(standard(cd), identity, vectors, 0)
    assert [
        [rank for e, rank in sectors if e[off]]
        for off in center_offsets
    ] == [[rank] for rank in ranks]


if __name__ == "__main__":
    print("Direct degree-two checks on random quivers:", random_checks())
    print("Direct degree-two checks on one-arrow rank pairs:", one_arrow_checks())
    for widths in ([4, 9, 4, 16], [2, 3, 0, 12], [4, 9, 2, 6]):
        center_profiles([0b11, 0b111, 0b1011, 0b10011], widths, widths)
    print("Factorization-free center profiles checked on three nonsplit direct products.")
