"""Compare degree-three ordinary PC with explicit GF(4) witnesses for binary 3-by-3 forms."""

from itertools import product

from check_binary_congruence import TruncatedPC, bit_polynomial, gf4_product


def pairing_table(a, vectors):
    pair = {}
    for x in vectors:
        left = [0] * 3
        for i, j in product(range(3), repeat=2):
            if a[3*i+j]:
                left[j] ^= x[i]
        for y in vectors:
            pair[x, y] = (gf4_product(left[0], y[0]) ^ gf4_product(left[1], y[1])
                          ^ gf4_product(left[2], y[2]))
    return pair


def orbit_representatives():
    vectors = list(product(range(2), repeat=3))
    basis = []
    for r in vectors[1:]:
        for s in vectors[1:]:
            if s == r:
                continue
            rs = tuple(x ^ y for x, y in zip(r, s))
            basis.extend((r, s, t) for t in vectors[1:] if t not in (r, s, rs))
    covered = set()
    reps = []
    for a in product(range(2), repeat=9):
        if a in covered:
            continue
        reps.append(a)
        pair = pairing_table(a, vectors)
        covered.update(tuple(pair[x, y] for x in rows for y in rows) for rows in basis)
    assert len(covered) == 512
    return reps


def raw_equations(a, b):
    for i, j in product(range(3), repeat=2):
        yield bit_polynomial(((3*i+k, 3*j+l) for k, l in product(range(3), repeat=2)
                              if a[3*k+l]), b[3*i+j])
        yield bit_polynomial(((3*i+k, 9+3*k+j) for k in range(3)), i == j)
        yield bit_polynomial(((9+3*i+k, 3*k+j) for k in range(3)), i == j)


def gf4_equivalent(b, pair, vectors):
    zero = (0, 0, 0)
    first, second, third = ([w for w in vectors if w != zero and pair[w, w] == b[4*i]]
                            for i in range(3))
    for x in first:
        line = {tuple(gf4_product(c, z) for z in x) for c in range(4)}
        for y in second:
            if y in line or pair[x, y] != b[1] or pair[y, x] != b[3]:
                continue
            plane = {tuple(z ^ gf4_product(c, t) for z, t in zip(v, y))
                     for v in line for c in range(4)}
            for w in third:
                if w not in plane and (pair[x, w], pair[y, w], pair[w, x], pair[w, y]) == (
                        b[2], b[5], b[6], b[7]):
                    return True
    return False


def kind(a):
    if not any(a):
        return 0
    if all(a[3*i+j] == a[3*j+i] for i, j in product(range(3), repeat=2)):
        return 2 if any(a[i] for i in (0, 4, 8)) else 1
    return 3


if __name__ == "__main__":
    reps = orbit_representatives()
    vectors = list(product(range(4), repeat=3))
    engines = {d: TruncatedPC(18, d) for d in (0, 2, 3)}
    counts = {}
    for a in reps:
        pair = pairing_table(a, vectors)
        for b in reps:
            expected = None
            if not gf4_equivalent(b, pair, vectors):
                if (not any(a) and any(b)) or (kind(a) == 1 and any(b[i] for i in (0, 4, 8))):
                    expected = 0
                elif kind(b) > kind(a):
                    expected = 2
                else:
                    expected = 3
            eq = list(raw_equations(a, b))
            got = next((d for d, engine in engines.items() if engine.refutes(eq)), None)
            assert got == expected, (a, b, got, expected)
            counts[got] = counts.get(got, 0) + 1
    print(f"{len(reps)} binary congruence representatives cover all 512 matrices. "
          f"Checked all {len(reps)**2} ordered representative pairs: {counts}.")
