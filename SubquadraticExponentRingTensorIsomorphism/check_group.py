"""Exact finite controls for the class-two group encoding of alternating bimaps."""

from itertools import product
from random import Random


class Model:
    def __init__(self, p, exponent, dimension, center_rank, coefficients):
        self.p = p
        self.n = p**exponent
        self.scale = 2 if p == 2 else 1
        self.nz = self.n * self.scale
        self.d = dimension
        self.m = center_rank
        self.ij = list((i, j) for i in range(dimension) for j in range(i + 1, dimension))
        self.coefficients = coefficients
        self.z0 = (0,) * center_rank
        self.v0 = (0,) * dimension
        self.identity = self.v0, self.z0

    def cocycle(self, left, right):
        out = [0] * self.m
        for i, j in self.ij:
            for k, coefficient in enumerate(self.coefficients[i, j]):
                out[k] += self.scale * left[i] * right[j] * coefficient
        return tuple(x % self.nz for x in out)

    def pairing(self, left, right):
        return tuple(((a - b) % self.nz) // self.scale
                     for a, b in zip(self.cocycle(left, right), self.cocycle(right, left)))

    def multiply(self, left, right):
        u, z = left
        v, w = right
        return add_mod(self.n, u, v), add_mod(self.nz, z, w, self.cocycle(u, v))

    def power(self, element, exponent):
        acc = self.identity
        for _ in range(exponent):
            acc = self.multiply(acc, element)
        return acc

    def adjusted_lift(self, value):
        power = self.power((value, self.z0), self.n)
        assert power[0] == self.v0
        center = tuple((-z // self.n) % self.scale for z in power[1])
        lift = value, center
        assert self.power(lift, self.n) == self.identity
        return lift

    def elements(self):
        return list(product(product(range(self.n), repeat=self.d),
                            product(range(self.nz), repeat=self.m)))


def add_mod(modulus, *vectors):
    return tuple(sum(components) % modulus for components in zip(*vectors))


def basis(dimension):
    return tuple(tuple(int(i == j) for i in range(dimension)) for j in range(dimension))


def apply_matrix(matrix, vector, modulus):
    return tuple(sum(a*b for a, b in zip(row, vector)) % modulus for row in matrix)


def make_invertible(p, modulus, dimension, randomness):
    result = list(map(list, basis(dimension)))
    for _ in range(6 * dimension):
        i, j = (randomness.randrange(dimension), randomness.randrange(dimension))
        if i == j:
            scalar = randomness.choice([x for x in range(modulus) if x % p])
            result[i] = [(scalar*x) % modulus for x in result[i]]
        else:
            scalar = randomness.randrange(modulus)
            result[i] = list(add_mod(modulus, result[i], [scalar*x for x in result[j]]))
    return result


def audit_pair(p, exponent, dimension, center_rank, rng, exhaustive_partner):
    n = p**exponent
    nz = n * (2 if p == 2 else 1)
    e = basis(dimension)
    coeffs = {(i, j): tuple(rng.randrange(n) for _ in range(center_rank))
              for i in range(dimension) for j in range(i + 1, dimension)}
    # The first slice is a symplectic form, so the simultaneous radical is zero.
    for (i, j), values in coeffs.items():
        coeffs[i, j] = (int(i % 2 == 0 and j == i + 1),) + values[1:]
    target = Model(p, exponent, dimension, center_rank, coeffs)
    a = make_invertible(p, n, dimension, rng)
    c_inv = make_invertible(p, nz, center_rank, rng)
    # Small test only: invert the center action by listing its basis preimages.
    inverse_columns = {}
    c_basis = basis(center_rank)
    for value in product(range(nz), repeat=center_rank):
        image = apply_matrix(c_inv, value, nz)
        if image in c_basis:
            inverse_columns[image] = value
    c = list(zip(*(inverse_columns[x] for x in c_basis)))
    ae = tuple(apply_matrix(a, x, n) for x in e)
    coeffs = {(i, j): apply_matrix(c_inv, target.pairing(ae[i], ae[j]), n)
              for i, j in target.ij}
    source = Model(p, exponent, dimension, center_rank, coeffs)
    lifts = tuple(target.adjusted_lift(x) for x in ae)

    def transporter(element):
        v, z = element
        # Descending basis order is the normal form with zero upper cocycle.
        point = target.v0, apply_matrix(c, z, nz)
        for generator, count in reversed(tuple(zip(lifts, v))):
            point = target.multiply(point, target.power(generator, count))
        return point

    vectors = tuple(product(range(n), repeat=dimension))
    for v in vectors:
        assert (all(target.pairing(v, x) == target.z0 for x in e)) == (v == target.v0)
        assert (all(source.pairing(v, x) == source.z0 for x in e)) == (v == source.v0)
        for model in (source, target):
            for z in (model.z0, model.m * (1,)):
                a_power, z_power = model.power((v, z), n)
                f = model.cocycle(v, v)
                assert a_power == model.v0
                assert z_power == tuple((n*w + n*(n-1)//2*t) % nz for w, t in zip(z, f))
            model.adjusted_lift(v)

    def random_element():
        return tuple(rng.randrange(n) for _ in range(dimension)), tuple(
            rng.randrange(nz) for _ in range(center_rank))

    if exhaustive_partner:
        elements = source.elements()
        decoded = {x: transporter(x) for x in elements}
        assert len(elements) == len(set(decoded.values()))
        for left, right in product(elements, repeat=2):
            assert target.multiply(decoded[left], decoded[right]) == decoded[source.multiply(left, right)]
        return len(vectors), len(elements)**2

    for _ in range(256):
        left, right = random_element(), random_element()
        assert target.multiply(transporter(left), transporter(right)) == transporter(source.multiply(left, right))
    return len(vectors), 256


if __name__ == "__main__":
    randomness = Random(210938)
    counts = [0, 0]
    cases = [(2, 1, 2, 1, True), (2, 2, 2, 1, True), (2, 3, 2, 1, False),
             (2, 2, 4, 2, False), (3, 1, 2, 1, True), (3, 2, 2, 2, False)]
    for case in cases:
        result = audit_pair(*case[:4], randomness, case[4])
        print(f"Parameters {case}. Quotient vectors, transporter product checks: {result}.")
        counts = [old + new for old, new in zip(counts, result)]
    print(f"Totals: {counts[0]} quotient vectors, {counts[1]} transporter product checks.")
