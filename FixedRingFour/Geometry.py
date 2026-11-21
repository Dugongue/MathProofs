"""Finite controls for tensor lifts in three local rings of order 125."""

from itertools import product
from random import Random

P = 5
DIMS = (3, 4, 4)
POSITIONS = tuple(product(*(range(d) for d in DIMS)))
INDEX = {position: i for i, position in enumerate(POSITIONS)}
GAUGE = tuple((mode, i, j) for mode, d in enumerate(DIMS)
              for i, j in product(range(d), repeat=2)
              if not (mode < 2 and i == j == 0))


def digits(value):
    return (value % P, value // P % P, value // (P * P))


class Ring:
    def __init__(self, model):
        self.model = model
        digits_table = tuple(digits(a) for a in range(P ** 3))
        self.add = [[0] * P ** 3 for _ in range(P ** 3)]
        self.mul = [[0] * P ** 3 for _ in range(P ** 3)]
        for a, (a0, a1, a2) in enumerate(digits_table):
            for b, (b0, b1, b2) in enumerate(digits_table):
                if model == "mixed":
                    self.add[a][b] = (a + b) % P ** 3
                    self.mul[a][b] = a * b % P ** 3
                else:
                    self.add[a][b] = ((a0 + b0) % P + P * ((a1 + b1) % P)
                                      + P ** 2 * ((a2 + b2) % P))
                    cross = a1 * b1 if model == "chain" else 0
                    self.mul[a][b] = (a0 * b0 % P + P * ((a0 * b1 + a1 * b0) % P)
                                      + P ** 2 * ((a0 * b2 + a2 * b0 + cross) % P))


def lift_pencil():
    def entry(i, j, k):
        if i == 0:
            return int(j == k)
        if i == 1:
            return j * int(j == k)
        return (j * j % P) * int(j == k) + int(k == j + 1)

    return [entry(*position) for position in POSITIONS]


def derivative(tensor):
    columns = []
    for mode, row, column in GAUGE:
        vector = [0] * len(tensor)
        for i, position in enumerate(POSITIONS):
            if position[mode] == column:
                target = position[:mode] + (row,) + position[mode + 1:]
                vector[INDEX[target]] = tensor[i]
        columns.append(vector)
    return [list(row) for row in zip(*columns)]


def pivot_rows(matrix):
    independent = []
    pivots = {}
    for i, initial in enumerate(matrix):
        row = initial[:]
        for j in sorted(pivots):
            factor = row[j] % P
            row = [(x - factor * y) % P for x, y in zip(row, pivots[j])]
        pivot = next((j for j, x in enumerate(row) if x % P), None)
        if pivot is not None:
            inv = pow(row[pivot] % P, -1, P)
            pivots[pivot] = [x * inv % P for x in row]
            independent.append(i)
    return independent


def inverse(matrix):
    n = len(matrix)
    rows = [row + [int(i == j) for j in range(n)] for i, row in enumerate(matrix)]
    for i in range(n):
        j = next(j for j in range(i, n) if rows[j][i] % P)
        rows[i], rows[j] = rows[j], rows[i]
        multiplier = pow(rows[i][i] % P, -1, P)
        rows[i] = [x * multiplier % P for x in rows[i]]
        for j in range(n):
            if j != i:
                factor = rows[j][i]
                rows[j] = [(a - factor * b) % P for a, b in zip(rows[j], rows[i])]
    return [row[n:] for row in rows]


def evaluate(ring, base, complement, coordinate):
    matrices = [[[int(i == j) for j in range(d)] for i in range(d)] for d in DIMS]
    for (mode, i, j), entry in zip(GAUGE, coordinate):
        matrices[mode][i][j] = ring.add[matrices[mode][i][j]][entry]
    tensor = base[:]
    for i, a in zip(complement, coordinate[len(GAUGE):]):
        tensor[i] = ring.add[tensor[i]][a]
    for mode, matrix in enumerate(matrices):
        transformed = []
        for position in POSITIONS:
            value = 0
            for j in range(DIMS[mode]):
                source = position[:mode] + (j,) + position[mode + 1:]
                term = ring.mul[matrix[position[mode]][j]][tensor[INDEX[source]]]
                value = ring.add[value][term]
            transformed.append(value)
        tensor = transformed
    return tensor


def check_normalizer():
    rng = Random(511)
    base = lift_pencil()
    jacobian = derivative(base)
    pivots = pivot_rows(jacobian)
    assert len(pivots) == len(GAUGE) == 39
    complement = [i for i in range(len(base)) if i not in pivots]
    assert len(complement) == 9
    matrix = [row + [int(i == j) for j in complement] for i, row in enumerate(jacobian)]
    inv = inverse(matrix)
    checks = []
    for model in ("mixed", "chain", "square-zero nonprincipal"):
        ring = Ring(model)
        for _ in range(24):
            sample = [P * rng.randrange(P ** 2) for _ in base]
            target = evaluate(ring, base, complement, sample)
            recovered = [0] * len(base)
            for place in (P, P ** 2):
                approximate = evaluate(ring, base, complement, recovered)
                delta = [((a // place) - (b // place)) % P
                         for a, b in zip(target, approximate)]
                correction = [sum(a * b for a, b in zip(row, delta)) % P for row in inv]
                recovered = [ring.add[word][place * value]
                             for word, value in zip(recovered, correction)]
            assert recovered == sample
            assert evaluate(ring, base, complement, recovered) == target
        checks.append((model, 24))
    return checks


def check_tame_burnside():
    answer = []
    for model in ("mixed", "chain", "square-zero nonprincipal"):
        ring = Ring(model)
        maximum_ideal = tuple(range(0, P ** 3, P))
        minus_one = next(u for u in range(P ** 3) if ring.add[u][1] == 0)
        action = lambda pair: (ring.mul[minus_one][pair[0]], pair[1])
        visited = set()
        orbits = 0
        for pair in product(maximum_ideal, repeat=2):
            if pair not in visited:
                orbits += 1
                visited.update((pair, action(pair)))
        formula = (25 ** 2 + 25) // 2
        assert orbits == formula == 325
        answer.append((model, orbits))
    return answer


if __name__ == "__main__":
    print("Congruence normalization witnesses:", check_normalizer())
    print("Tame sign-action Burnside controls:", check_tame_burnside())
