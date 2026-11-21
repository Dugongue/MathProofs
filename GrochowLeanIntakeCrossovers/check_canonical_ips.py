from fractions import Fraction
from itertools import product
from collections import namedtuple

Field = namedtuple("Field", "label constant add mul inverse r")


def gf4_mul(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 0b111
    return result


FIELDS = [
    Field("Q", Fraction, lambda a, b: a + b, lambda a, b: a * b,
          lambda a: 1 / a, Fraction(1)),
    Field("F3", lambda a: a % 3, lambda a, b: (a + b) % 3,
          lambda a, b: a * b % 3, lambda a: pow(a, -1, 3), 1),
    Field("F4", lambda a: a % 2, lambda a, b: a ^ b, gf4_mul,
          lambda a: gf4_mul(a, a), 2),
]


def check_projection(field, arity, accepted):
    """Enumerate satisfying assignments of a negative 2-CNF as independent sets."""
    number = field.constant
    add, mul, inv = field.add, field.mul, field.inverse
    zero, one, minus_one = map(number, (0, 1, -1))

    def sub(a, b):
        return add(a, mul(minus_one, b))

    r = field.r
    s = sub(minus_one, r)
    alpha = mul(r, inv(add(one, r)))
    beta = mul(s, inv(add(one, s)))
    c = mul(sub(one, alpha), sub(one, beta))
    selector_weight = alpha
    delta = mul(selector_weight, sub(one, selector_weight))

    selectors = [(2 * i, 2 * i + 1) for i in range(arity)]
    features = list(range(2 * arity, 3 * arity))
    values = [selector_weight] * (2 * arity) + [None] * arity
    edges = list(selectors)
    disjunctions = 0

    def simulate(variables):
        nonlocal disjunctions
        disjunctions += 1
        a, b = len(values), len(values) + 1
        values.extend((alpha, beta))
        edges.append((a, b))
        for v in set(variables):
            edges.extend(((a, v), (b, v)))

    for pair in selectors:
        simulate(pair)
    for bit_vector in product((0, 1), repeat=arity):
        if bit_vector not in accepted:
            simulate(selectors[i][1 - bit] for i, bit in enumerate(bit_vector))
    for pair, feature in zip(selectors, features):
        simulate((pair[0], feature))

    neighbors = [0] * len(values)
    for a, b in edges:
        neighbors[a] |= 1 << b
        neighbors[b] |= 1 << a

    def independent_sets(available, chosen=0):
        if not available:
            yield chosen
            return
        bit = available & -available
        v = bit.bit_length() - 1
        remaining = available ^ bit
        yield from independent_sets(remaining, chosen)
        yield from independent_sets(remaining & ~neighbors[v], chosen | bit)

    scale = one
    for _ in range(arity):
        scale = mul(scale, inv(delta))
    for _ in range(disjunctions):
        scale = mul(scale, inv(c))

    coefficients = [zero] * (1 << arity)
    for mask in independent_sets((1 << len(values)) - 1):
        weight = scale
        term = {0: one}
        for v, value in enumerate(values):
            chosen = bool(mask & (1 << v))
            if value is not None:
                weight = mul(weight, value if chosen else sub(one, value))
                continue
            bit = 1 << (v - 2 * arity)
            shifted = {k | bit: z if chosen else mul(minus_one, z)
                       for k, z in term.items()}
            term = shifted if chosen else term | shifted
        for k, coefficient in term.items():
            coefficients[k] = add(coefficients[k], mul(weight, coefficient))

    expected = [zero] * (1 << arity)
    for accepted_vector in accepted:
        monomial = sum(bit << i for i, bit in enumerate(accepted_vector))
        expected[monomial] = add(expected[monomial], one)
    assert coefficients == expected, (field.label, accepted, coefficients, expected)


if __name__ == "__main__":
    truth_inputs = list(product((0, 1), repeat=2))
    count = 0
    for field in FIELDS:
        for mask in range(1 << len(truth_inputs)):
            accepted = {item for i, item in enumerate(truth_inputs) if mask & (1 << i)}
            check_projection(field, 2, accepted)
            count += 1
    print(f"{count} exact polynomial checks passed")
