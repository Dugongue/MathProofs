"""Small exact controls for the last-digit tensor chart and incidence."""

from itertools import product
from random import Random

P = 3
N = 4
BASIS = tuple(tuple(int(i == j) for i in range(N)) for j in range(N))


class Ring:
    def __init__(self, mixed):
        self.add = [[0] * 9 for _ in range(9)]
        self.mul = [[0] * 9 for _ in range(9)]
        for a, b in product(range(9), repeat=2):
            if mixed:
                self.add[a][b], self.mul[a][b] = (a + b) % 9, a * b % 9
            else:
                a0, a1, b0, b1 = a % 3, a // 3, b % 3, b // 3
                self.add[a][b] = (a0 + b0) % 3 + 3 * ((a1 + b1) % 3)
                self.mul[a][b] = a0 * b0 % 3 + 3 * ((a0 * b1 + a1 * b0) % 3)
        self.neg = [row.index(0) for row in self.add]
        self.inv = {i: row.index(1) for i, row in enumerate(self.mul) if i % 3}
        self.n = self.sum([1] * N)

    def sum(self, values):
        result = 0
        for x in values:
            result = self.add[result][x]
        return result

    def dot(self, x, y):
        return self.sum(self.mul[a][b] for a, b in zip(x, y))

    def apply(self, matrix, vector):
        return tuple(self.dot(row, vector) for row in matrix)

    def subtract_multiple(self, x, y, factor):
        return tuple(self.add[a][self.neg[self.mul[factor][b]]] for a, b in zip(x, y))

    def inverse(self, matrix):
        rows = [tuple(row) + BASIS[i] for i, row in enumerate(matrix)]
        for i in range(N):
            pivot = next((j for j in range(i, N) if rows[j][i] in self.inv), None)
            if pivot is None:
                return None
            rows[i], rows[pivot] = rows[pivot], rows[i]
            multiplier = self.inv[rows[i][i]]
            rows[i] = tuple(self.mul[multiplier][a] for a in rows[i])
            for j in range(N):
                if j != i:
                    rows[j] = self.subtract_multiple(rows[j], rows[i], rows[j][i])
        return tuple(row[N:] for row in rows)

    def unitized(self, a, b):
        last = (3 * (a[1] % 3) * (b[2] % 3)) % 9
        result = [self.mul[a[0]][b[0]]]
        for i in range(1, N):
            result.append(self.add[self.mul[a[0]][b[i]]][self.mul[b[0]][a[i]]])
        result[3] = self.add[result[3]][last]
        return tuple(result)


def field_rank(matrix, p=3):
    rows = [[x % p for x in row] for row in matrix]
    rank = 0
    for i in range(len(rows[0])):
        pivot = next((j for j in range(rank, len(rows)) if rows[j][i]), None)
        if pivot is None:
            continue
        rows[pivot], rows[rank] = rows[rank], rows[pivot]
        inv = pow(rows[rank][i], -1, p)
        for j in range(rank + 1, len(rows)):
            factor = rows[j][i] * inv % p
            rows[j] = [(a - factor * b) % p for a, b in zip(rows[j], rows[rank])]
        rank += 1
    return rank


def check_chart(mixed):
    ring = Ring(mixed)
    rng = Random(2028)
    successes = 0
    for _ in range(200):
        matrices = []
        for _ in range(3):
            rows = list(BASIS)
            for _ in range(6):
                i, j = rng.sample(range(N), 2)
                rows[i] = ring.subtract_multiple(rows[i], rows[j], rng.randrange(9))
            matrices.append(tuple(rows))
        first, second, output = matrices

        def tensor(x, y):
            return ring.apply(output, ring.unitized(ring.apply(first, x),
                                                   ring.apply(second, y)))

        a = tuple(zip(*(tensor(v, BASIS[0]) for v in BASIS)))
        b = tuple(zip(*(tensor(BASIS[0], v) for v in BASIS)))
        u = tensor(BASIS[0], BASIS[0])
        ai, bi = ring.inverse(a), ring.inverse(b)
        if ai is None or bi is None or u[0] % 3 == 0:
            continue

        def normal(x, y):
            return tensor(ring.apply(ai, x), ring.apply(bi, y))

        def trace(x):
            return ring.mul[ring.inv[ring.n]][ring.sum(normal(x, v)[i]
                                                      for i, v in enumerate(BASIS))]

        framed = (u,) + tuple(ring.subtract_multiple(v, u, trace(v)) for v in BASIS[1:])
        change = tuple(zip(*framed))
        inverse_change = ring.inverse(change)
        assert inverse_change is not None
        for v in BASIS:
            assert normal(v, u) == normal(u, v) == v
        full = []
        for i, j in product(range(N), repeat=2):
            assert normal(ring.apply(a, BASIS[i]), ring.apply(b, BASIS[j])) == tensor(BASIS[i], BASIS[j])
            if i and j:
                value = ring.apply(inverse_change, normal(framed[i], framed[j]))
                assert value[0] == 0 and all(x % 3 == 0 for x in value)
                full.append(tuple(x // 3 for x in value[1:]))
        assert field_rank(full) == 1
        assert field_rank([sum((full[3 * i + j] for j in range(3)), ())
                           for i in range(3)]) == 1
        assert field_rank([sum((full[3 * i + j] for i in range(3)), ())
                           for j in range(3)]) == 1
        for i in range(3):
            assert sum(full[3 * i + j][j] for j in range(3)) % 3 == 0
        successes += 1
        if successes == 24:
            break
    assert successes == 24
    return successes


def gf4_mul(a, b):
    result = 0
    for i in range(2):
        if b >> i & 1:
            result ^= a << i
    return result ^ 7 if result >> 2 else result


def witt2_char2_mul(x, y):
    a, b = x
    c, d = y
    return gf4_mul(a, c), gf4_mul(gf4_mul(a, a), d) ^ gf4_mul(b, gf4_mul(c, c))


def check_witt_twist():
    distinct_from_untwisted = 0
    for a, b, last in product(range(4), repeat=3):
        result = witt2_char2_mul((a, b), (0, last))
        assert result[0] == 0
        assert result[1] == gf4_mul(gf4_mul(a, a), last)
        distinct_from_untwisted += result[1] != gf4_mul(a, last)
    assert distinct_from_untwisted == 24
    return distinct_from_untwisted


def check_rank_one_flags():
    normals = tuple(vec for vec in product(range(5), repeat=3)
                    if next((c for c in vec if c), 0) == 1)
    planes = {frozenset(v for v in product(range(5), repeat=3)
                        if sum(x * y for x, y in zip(v, normal)) % 5 == 0)
              for normal in normals}
    assert len(planes) == 31 and all(len(plane) == 25 for plane in planes)
    return len(planes) ** 2


if __name__ == "__main__":
    print("Equal- and mixed-characteristic chart transports:", check_chart(False), check_chart(True))
    print("Witt final-ideal cases where the twist is visible:", check_witt_twist())
    print("Rational flags over one rank-one target:", check_rank_one_flags())
