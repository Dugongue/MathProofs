"""Check the substitution in the printed equations and the fixed companion tag."""

from itertools import product
from random import Random


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def zero(n):
    return [[0] * n for _ in range(n)]


def blocks(grid):
    return [sum((block[i] for block in row), [])
            for row in grid for i in range(len(row[0]))]


def diagonal(*items):
    return blocks([[item if i == j else zero(len(item)) for j in range(len(items))]
                   for i, item in enumerate(items)])


def tr(a):
    return list(map(list, zip(*a)))


def plus(a, b, p, sign=1):
    return [[(x + sign*y) % p for x, y in zip(r, s)] for r, s in zip(a, b)]


def mul(a, b, p):
    cols = tr(b)
    return [[sum(x*y for x, y in zip(r, c)) % p for c in cols] for r in a]


def hyper(a):
    n = len(a)
    return blocks([[zero(n), identity(n)], [a, zero(n)]])


def rank(a, p):
    a = [row.copy() for row in a]
    lead = 0
    for j in range(len(a[0])):
        k = next((k for k in range(lead, len(a)) if a[k][j]), None)
        if k is None:
            continue
        a[k], a[lead] = a[lead], a[k]
        inv = pow(a[lead][j], -1, p)
        for i in range(lead + 1, len(a)):
            scale = inv * a[i][j]
            a[i] = [(x - scale*y) % p for x, y in zip(a[i], a[lead])]
        lead += 1
    return lead


def check_tag(a, p):
    n = len(a)
    w = blocks([[zero(n), a], [zero(n), zero(n)]])
    eye, z = identity(2*n), zero(2*n)
    tag = blocks([[z, z, plus(eye, w, p)], [eye, z, eye], [z, eye, z]])
    cube = mul(mul(tag, tag, p), tag, p)
    f = plus(plus(cube, tag, p, -1), identity(6*n), p, -1)
    assert f == diagonal(w, w, w)
    assert rank(f, p) == 3 * rank(a, p)
    assert rank(tag, p) == 6*n
    assert hyper(tag) != tr(hyper(tag))


def check_substitution(m, n, z, w, p):
    x = diagonal(tr(w), z)
    gram = mul(mul(x, hyper(m), p), tr(x), p)
    zw = mul(z, w, p)
    delta = plus(mul(z, m, p), mul(n, z, p), p, -1)
    lower = plus(mul(delta, w, p), mul(n, zw, p), p)
    assert gram == blocks([[zero(len(m)), tr(zw)], [lower, zero(len(m))]])


if __name__ == "__main__":
    rng = Random(73)
    tag_count = sub_count = 0
    for p in (2, 3, 5, 23):
        values = product(range(p), repeat=4) if p <= 3 else (
            [rng.randrange(p) for _ in range(4)] for _ in range(32))
        for a, b, c, d in values:
            m = [[a, b], [c, d]]
            check_tag(m, p)
            tag_count += 1
            args = [[[rng.randrange(p) for _ in range(2)] for _ in range(2)]
                    for _ in range(3)]
            check_substitution(m, *args, p)
            sub_count += 1
    print(f"Verified {tag_count} companion tags and {sub_count} raw substitutions, including characteristic 23.")
