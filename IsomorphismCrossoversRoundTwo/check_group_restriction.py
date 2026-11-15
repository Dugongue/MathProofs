"""Finite check of joint restriction on four central classes of PSL(2,5) × C2."""

from itertools import product


def multiply(x, y):
    a, b, c, d = x
    e, f, g, h = y
    return ((a * e + b * g) % 5, (a * f + b * h) % 5,
            (c * e + d * g) % 5, (c * f + d * h) % 5)


def negate(x):
    return tuple(-a % 5 for a in x)


def quotient_table():
    identity = (1, 0, 0, 1)
    representatives = sorted({min(x, negate(x)) for x in product(range(5), repeat=4)
                              if (x[0] * x[3] - x[1] * x[2]) % 5 == 1})
    representatives.remove(identity)
    representatives.insert(0, identity)
    index = {x: i for i, x in enumerate(representatives)}
    index.update({negate(x): i for i, x in enumerate(representatives)})
    table, signs = [], []
    for x in representatives:
        products = [multiply(x, y) for y in representatives]
        row = [index[z] for z in products]
        table.append(row)
        signs.append([int(z != representatives[i]) for z, i in zip(products, row)])
    return table, signs


def coboundary(table, rhs):
    """Test c(x,y)=v(x)+v(y)+v(xy) by linear elimination over F2."""
    n = len(table)
    basis = {}
    for a in range(n):
        for b in range(n):
            mask = (1 << a) ^ (1 << b) ^ (1 << table[a][b])
            value = rhs(a, b)
            while mask:
                pivot = mask.bit_length()
                if pivot not in basis:
                    basis[pivot] = mask, value
                    break
                previous, bit = basis[pivot]
                mask ^= previous
                value ^= bit
            if not mask and value:
                return False
    return True


def main():
    socle, signs = quotient_table()
    assert len(socle) == 60
    n = 2 * len(socle)
    table = [[2 * socle[a // 2][b // 2] + ((a ^ b) & 1) for b in range(n)] for a in range(n)]
    cyclic = [[0, 1], [1, 0]]
    for alpha, beta in product((0, 1), repeat=2):
        whole = coboundary(table, lambda a, b: alpha * signs[a // 2][b // 2] ^ beta * (a & b & 1))
        on_s = coboundary(socle, lambda a, b: alpha * signs[a][b])
        on_j = coboundary(cyclic, lambda a, b: beta * a * b)
        assert (on_s, on_j) == (alpha == 0, beta == 0)
        assert whole == (on_s and on_j)
    print('PASS: joint restriction distinguishes all four tested extension classes')


if __name__ == '__main__':
    main()
