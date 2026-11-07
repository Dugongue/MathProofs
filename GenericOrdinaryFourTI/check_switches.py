"""Check the integer switch and its sum-preserving permutation extension."""
from itertools import permutations, product


def verify(n):
    shifts = (0, 1, 3, 2)
    t = (1, 3, -1, -3)
    x = [(-t[i] - t[(i + 1) % 4]) for i in range(4)]

    def row(a, b):
        return tuple(z % n for z in (a, 3 * b, -a - b, 2 * a + 4 * b))

    plus = [row(x[i], t[(i + 1) % 4]) for i in range(4)]
    minus = [row(x[i], t[i]) for i in range(4)]
    rows = plus + minus
    assert len(set(rows)) == 8
    h = {(b - a) % n: (d - c) % n for a, b, c, d in rows}
    f = {(b - a) % n: (c - a) % n for a, b, c, d in rows}
    assert len(h) == len(set(h.values())) == 8
    parity_classes = (range(0, n, 2), range(1, n, 2)) if n % 2 == 0 else (range(n),)
    for indices in parity_classes:
        inputs = [i for i in indices if i not in h]
        outputs = [i for i in indices if i not in h.values()]
        assert len(inputs) == len(outputs)
        h.update(zip(inputs, outputs))
    for i in range(n):
        if i not in f:
            f[i] = next(z for z in range(n) if (2 * z - i + h[i]) % n == 0)

    def route(a, b):
        shift = f[(b - a) % n]
        return (a + shift) % n, (b - shift) % n

    assert len({route(a, b) for a, b in product(range(n), repeat=2)}) == n**2
    assert all(route(a, b) == (c, d) for a, b, c, d in rows)
    assert all((a + b - c - d) % n == 0 for a, b, c, d in rows)
    assert all(plus[i][j] == minus[(i + s) % 4][j]
               for i in range(4) for j, s in enumerate(shifts))
    valid = [
        (p, m)
        for p in permutations(range(4))
        for m in permutations(range(4))
        if all(plus[p[i]][j] == minus[m[(i + s) % 4]][j]
               for i in range(4) for j, s in enumerate(shifts))
    ]
    assert len(valid) == 4
    for j in range(4):
        labels = {plus[p[0]][j] for p, _ in valid}
        assert len(labels) == 4
        assert all({(i + k) % n for i in labels} != labels for k in range(1, n))


if __name__ == "__main__":
    for side in (37, 38, 40, 42, 53):
        verify(side)
    print("PASS: exact routing, matching, unit monomial coefficients and aperiodicity.")
