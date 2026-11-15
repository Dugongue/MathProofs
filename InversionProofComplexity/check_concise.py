"""Exact finite and symbolic controls for the concise tensor separation."""

from collections import Counter
from itertools import product
from random import Random


def block_tensor(matrix_blocks, scalar_blocks, padding):
    table = {}
    for block in range(matrix_blocks):
        base = 4 * block
        for i, j, k in product(range(2), repeat=3):
            table[base + 2*i + j, base + 2*j + k, base + 2*i + k] = 1
    for coordinate in range(4 * matrix_blocks, 4 * (matrix_blocks + scalar_blocks) + padding):
        table[coordinate, coordinate, coordinate] = 1
    return table


def projected_action(r, s, padding):
    dimension = 4 * (r + s) + padding
    source = block_tensor(r, s, padding)
    target = block_tensor(s, r, padding)
    rows_for_column = [[] for _ in range(dimension)]
    for i, j, inner in product(range(r), range(s), range(4)):
        rows_for_column[4*i + inner].append((4*j + inner, (i, j)))
        rows_for_column[4*(r + j) + inner].append((4*(s + i) + inner, (i, j)))
    for coordinate in range(dimension - padding, dimension):
        rows_for_column[coordinate].append((coordinate, None))

    calculated = {}
    for key in source:
        for entries in product(*(rows_for_column[v] for v in key)):
            out = tuple(row for row, _ in entries)
            support = frozenset(edge for _, edge in entries if edge is not None)
            if len({i for i, _ in support}) < len(support) or len({j for _, j in support}) < len(support):
                continue
            calculated.setdefault(out, Counter())[support] += 1

    wanted = {}
    for key in target:
        coordinate = key[0]
        if coordinate < 4*s:
            expected = [frozenset({(i, coordinate//4)}) for i in range(r)]
        elif coordinate < 4*(r+s):
            expected = [frozenset({(coordinate//4 - s, j)}) for j in range(s)]
        else:
            expected = [frozenset()]
        wanted[key] = Counter(expected)
    assert calculated == wanted


def constant_degree_identities(prime, rng):
    for _ in range(500):
        a, b, aa, bb, u, v, x, y, xx, yy, ab, ba = (
            rng.randrange(prime) for _ in range(12)
        )
        delta = ab - ba
        substitution = (
            a*b*((ab - x*yy) - (ba - xx*y))
            - (u - x*b)*a*yy - u*(v - a*yy)
            + (v - xx*b)*a*y + v*(u - a*y)
        )
        assert (a*b*delta - substitution) % prime == 0
        assert (aa*(a*b*delta) - (a*aa - 1)*b*delta - b*delta) % prime == 0
        assert (bb*(b*delta) - (b*bb - 1)*delta - delta) % prime == 0


def rank_padding(r, s, prime, rng):
    q = [[rng.randrange(prime) for _ in range(s)] + [0]*(r-s) for _ in range(r)]
    p = [[rng.randrange(prime) for _ in range(r)] for _ in range(s)] + [[0]*r for _ in range(r-s)]
    last = sum(p[-1][i] * q[i][-1] for i in range(r)) - 1
    assert last % prime == (prime - 1)


def main():
    for r, s, h in ((2, 1, 0), (3, 2, 1), (4, 3, 4), (5, 1, 1), (8, 6, 2)):
        projected_action(r, s, h)
    rng = Random(115)
    for p in (2, 3, 5, 7, 13):
        constant_degree_identities(p, rng)
        rank_padding(9, 6, p, rng)
    print('PASS: 5 symbolic tensor projections, 7500 scalar identities, 5 padded inversion checks')


if __name__ == '__main__':
    main()
