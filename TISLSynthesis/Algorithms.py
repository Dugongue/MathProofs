"""Exact small controls for root triples and pencil determinant tests."""

from itertools import permutations, product


ZERO = (0, 0, 0)
ONE = (1, 0, 0)
FINITE = tuple(product(range(3), repeat=3))
RATIONAL = tuple((i, 0, 0) for i in range(3))


def add(a, b):
    return tuple((x + y) % 3 for x, y in zip(a, b))


def negate(a):
    return tuple(-x % 3 for x in a)


def mul(a, b):
    raw = [0] * 5
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            raw[i + j] += x * y
    # The extension field has a^3 = a + 1.
    for i in (4, 3):
        raw[i - 3] += raw[i]
        raw[i - 2] += raw[i]
    return tuple(x % 3 for x in raw[:3])


def power(a, index):
    out = ONE
    while index:
        if index & 1:
            out = mul(out, a)
        a = mul(a, a)
        index //= 2
    return out


def bracket(v, w):
    return add(mul(v[0], w[1]), negate(mul(v[1], w[0])))


def normalize(vector):
    pivot = next(x for x in vector if x != ZERO)
    inverse = power(pivot, 25)
    return tuple(mul(x, inverse) for x in vector)


def projectivities():
    return {
        normalize((a, b, c, d))
        for a, b, c, d in product(RATIONAL, repeat=4)
        if bracket((a, b), (c, d)) != ZERO
    }


def frame(s):
    p, q, r = s
    scale_p, scale_q = bracket(r, q), bracket(r, p)
    return (
        mul(scale_p, p[1]), negate(mul(scale_p, p[0])),
        mul(scale_q, q[1]), negate(mul(scale_q, q[0])),
    )


def product2(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return (
        add(mul(a, e), mul(b, g)),
        add(mul(a, f), mul(b, h)),
        add(mul(c, e), mul(d, g)),
        add(mul(c, f), mul(d, h)),
    )


def apply(matrix, point):
    a, b, c, d = matrix
    x, y = point
    return normalize((add(mul(a, x), mul(b, y)), add(mul(c, x), mul(d, y))))


def roots_control():
    # Over F_3 every value of t^3-t-1 is -1. Its derivative is -1.
    roots = {
        normalize((u, ONE)) for u in FINITE if add(power(u, 3), negate(u)) == ONE
    }
    assert len(roots) == 3 and all(not all(x in RATIONAL for x in point) for point in roots)
    candidates = set()
    for source, target in product(permutations(roots), repeat=2):
        a, b, c, d = frame(source)
        m = normalize(product2((d, negate(b), negate(c), a), frame(target)))
        assert [apply(m, point) for point in target] == list(source)
        candidates.add(m)
    descended = {m for m in candidates if all(power(x, 3) == x for x in m)}
    full_projective_group = projectivities()
    assert len(full_projective_group) == 24
    direct = {m for m in full_projective_group if {apply(m, p) for p in roots} == roots}
    assert len(candidates) == 6 and len(descended) == 3 and descended == direct
    print("irreducible cubic: six geometric projectivities, three over F_3")


def determinant_control():
    nilpotent = (ZERO, ONE, ZERO, ZERO)
    centralizer_dets = {
        bracket(m[:2], m[2:])
        for m in product(RATIONAL, repeat=4)
        if bracket(m[:2], m[2:]) != ZERO
        and product2(m, nilpotent) == product2(nilpotent, m)
    }
    assert centralizer_dets == {ONE}

    zero_root = (ZERO, ONE)
    infinity = (ONE, ZERO)
    minus_one = (ONE, (2, 0, 0))
    points = [zero_root, minus_one, infinity]
    fixed = {m for m in projectivities() if [apply(m, p) for p in points] == points}
    assert fixed == {(ONE, ZERO, ZERO, ONE)}
    assert {a for a in RATIONAL if power(a, 2) == ONE and power(a, 12) == ONE} == {
        ONE, (2, 0, 0)
    }
    assert all(mul((2, 0, 0), a) != ONE for a in centralizer_dets)
    print("square determinant subgroup excludes the sign-twisted Jordan pencil")

    rational_lines = {normalize(v) for v in product(RATIONAL, repeat=2) if v != (ZERO, ZERO)}
    singular = {
        (x, y) for x, y in rational_lines
        if ZERO in (x, y, add(x, negate(y)), add(x, y))
    }
    assert len(singular) == len(rational_lines) == 4
    print("diagonal pencil: all four rational slices singular, determinant nonzero")


if __name__ == "__main__":
    roots_control()
    determinant_control()

