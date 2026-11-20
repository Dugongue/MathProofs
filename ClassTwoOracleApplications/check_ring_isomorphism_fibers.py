"""Exact finite checks for the unmarked ring and bimap fiber calculations."""

from itertools import product
from math import gcd, lcm
from random import Random


def units(modulus):
    return tuple(a for a in range(modulus) if gcd(a, modulus) == 1)


def check_gauges():
    checked = 0
    for modulus in (2, 4, 8, 9, 25):
        all_units = units(modulus)
        for h, h1, h2, d1, d2 in product(all_units, repeat=5):
            normalized = h1 * pow(h2, -1, modulus) % modulus
            new_h1 = h * pow(d1, -1, modulus) * h1 % modulus
            new_h2 = h * pow(d2, -1, modulus) * h2 % modulus
            raw_change = d1 * pow(d2, -1, modulus) % modulus
            assert new_h1 * pow(new_h2, -1, modulus) * raw_change % modulus == normalized
            checked += 1
    return checked


def check_mixed_bimaps(rng):
    checked = 0
    for p in (2, 3, 5):
        for a, b, c in product(range(1, 4), repeat=3):
            u, v, w = p**a, p**b, p**c
            modulus = max(u, v, w)
            scalar_choices = units(modulus)
            # These choices produce a genuinely biadditive cyclic map.
            coefficient = lcm(w // gcd(u, w), w // gcd(v, w))

            def bimap(x, y):
                return coefficient * x * y % w

            for _ in range(16):
                x, y = rng.randrange(u), rng.randrange(v)
                h0, h1, h2 = (rng.choice(scalar_choices) for _ in range(3))
                k01, k12, k02 = h0 * pow(h1, -1, modulus), h1 * pow(h2, -1, modulus), h0 * pow(h2, -1, modulus)
                assert bimap(k01 * x % u, k12 * y % v) == k02 * bimap(x, y) % w
                checked += 1
    return checked


def check_heisenberg(p, e, rng):
    modulus = p**e
    one = (1, 0, 0, 1)
    zero = (0, 0, 0, 0)

    def add(x, y):
        return tuple((a + b) % modulus for a, b in zip(x, y))

    def scale(k, x):
        return tuple(k * a % modulus for a in x)

    def mul(x, y):
        return tuple(sum(x[2*i + k] * y[2*k + j] for k in range(2)) % modulus
                     for i in range(2) for j in range(2))

    def determinant(x):
        return (x[0] * x[3] - x[1] * x[2]) % modulus

    def inverse(x):
        return scale(pow(determinant(x), -1, modulus), (x[3], -x[1], -x[2], x[0]))

    invertible = tuple(x for x in product(range(modulus), repeat=4) if gcd(determinant(x), modulus) == 1)
    assert len(invertible) == p ** (4 * (e - 1)) * (p*p - 1) * (p*p - p)

    def random_matrix():
        return tuple(rng.randrange(modulus) for _ in range(4))

    def group_mul(g, h):
        x, y, z = g
        a, b, c = h
        return add(x, a), add(y, b), add(add(z, c), mul(x, b))

    def group_pow(g, n):
        result = zero, zero, zero
        for _ in range(n):
            result = group_mul(result, g)
        return result

    def automorphism(left, right, conjugator, shift_left, shift_right, g):
        x, y, z = g
        cinv = inverse(conjugator)

        def theta(a):
            return mul(mul(conjugator, a), cinv)

        shift = add(mul(x, shift_left), mul(shift_right, y))
        return mul(left, theta(x)), mul(theta(y), right), add(mul(mul(left, theta(z)), right), shift)

    tested = 0
    for _ in range(80):
        params = tuple(rng.choice(invertible) for _ in range(3)) + (random_matrix(), random_matrix())
        g, h = tuple(random_matrix() for _ in range(3)), tuple(random_matrix() for _ in range(3))
        assert automorphism(*params, group_mul(g, h)) == group_mul(
            automorphism(*params, g), automorphism(*params, h)
        )
        u, v, _, _, _ = params
        assert automorphism(*params, (one, zero, zero))[0] == u
        assert automorphism(*params, (zero, one, zero))[1] == v
        x, y, z = g
        assert group_pow(g, modulus) == (zero, zero, scale(modulus * (modulus - 1) // 2, mul(x, y)))
        tested += 4
    identity_pair = one, one, zero
    assert group_pow(identity_pair, modulus) == (zero, zero, zero if p != 2 else scale(modulus // 2, one))
    return len(invertible), tested + 1


if __name__ == "__main__":
    rng = Random(27112026)
    print("Exact gauge changes:", check_gauges())
    print("Mixed cyclic bimap changes:", check_mixed_bimaps(rng))
    result = tuple(check_heisenberg(p, e, rng) for p, e in ((2, 1), (2, 2), (2, 3), (3, 1), (3, 2)))
    print("Invertible matrices counted:", sum(x for x, _ in result))
    print("Heisenberg laws and powers:", sum(y for _, y in result))
