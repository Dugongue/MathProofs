"""Exact finite controls for embedded-subgroup transport."""

from collections import Counter
from itertools import product
from math import gcd
import random


def normalized_unit(a, b, u, modulus):
    return u * pow(a * b, -1, modulus) % modulus


def check_corner_alignment():
    rng = random.Random(261120)
    tested = 0
    for modulus in (2, 3, 4, 5, 8, 9, 16, 25, 27, 32):
        units = [x for x in range(modulus) if gcd(x, modulus) == 1]
        cases = (
            product(units, repeat=6)
            if len(units) < 5
            else (rng.choices(units, k=6) for _ in range(500))
        )
        for a, b, u, source, middle, target in cases:
            scalar_a = middle * pow(target, -1, modulus) % modulus
            scalar_b = source * pow(middle, -1, modulus) % modulus
            scalar_z = source * pow(target, -1, modulus) % modulus
            assert normalized_unit(a * scalar_a, b * scalar_b, u * scalar_z, modulus) == (
                normalized_unit(a, b, u, modulus)
            )
            tested += 1
    return tested


def check_subgroups(prime):
    prime2 = prime**2

    def add(u, v):
        return ((u[0] + v[0]) % prime2, (u[1] + v[1]) % prime, (u[2] + v[2]) % prime)

    def scalar(t, u):
        return (t * u[0] % prime2, t * u[1] % prime, t * u[2] % prime)

    def bracket(u, v):
        return (0, 0, (u[0] * v[1] - v[0] * u[1]) % prime)

    inverse_two = pow(2, -1, prime)

    def multiply(u, v):
        return add(add(u, v), scalar(inverse_two, bracket(u, v)))

    def commutator(u, v):
        return multiply(multiply(multiply(scalar(-1, u), scalar(-1, v)), u), v)

    def pair_span(u, v):
        return frozenset(add(scalar(a, u), scalar(b, v))
                         for a, b in product(range(prime), repeat=2))

    px, y, z = (prime, 0, 0), (0, 1, 0), (0, 0, 1)
    left = pair_span(px, y)
    right = pair_span(add(px, z), y)
    central_derived = {scalar(a, z) for a in range(prime)}
    assert left & central_derived == right & central_derived == {(0, 0, 0)}
    assert {u[:2] for u in left} == {u[:2] for u in right}
    assert px in left and px not in right
    assert commutator((1, 0, 0), y) == z
    assert z not in left and z not in right
    for marked in (left, right):
        assert all(multiply(u, v) in marked for u, v in product(marked, repeat=2))
        assert {scalar(a, u) for a in range(prime) for u in marked} == marked

    x_images = [(a, b, c) for a, b, c in product(range(prime2), range(prime), range(prime))
                 if a % prime]
    y_images = [(a * prime, b, c)
                for a, b, c in product(range(prime), range(1, prime), range(prime))]
    # Every additive automorphism has precisely this type of images of x and y.
    # The bracket uniquely forces the image of z in the characteristic derived line.
    fibres = Counter()
    images_of_left = set()
    aut_count = 0
    for x_image, y_image in product(x_images, y_images):
        z_image = bracket(x_image, y_image)
        assert z_image != (0, 0, 0)
        px_image = scalar(prime, x_image)
        image = pair_span(px_image, y_image)
        assert image != right
        images_of_left.add(image)
        aut_count += 1
        if image == left:
            fibres[(px_image, y_image)] += 1

    assert aut_count == prime**5 * (prime - 1)**2
    assert len(images_of_left) == prime
    assert sum(fibres.values()) == prime**4 * (prime - 1)**2
    assert len(fibres) == prime * (prime - 1)**2
    assert set(fibres.values()) == {prime**3}
    return aut_count, len(fibres)



def check_exterior_coefficients():
    coefficients = {}
    for p in (5, 7, 11, 13):
        letters = (0, 1, 0, *range(2, p - 1))
        bracket = Counter({(letters[0],): 1})
        for letter in letters[1:]:
            next_bracket = Counter()
            for word, coefficient in bracket.items():
                next_bracket[word + (letter,)] += coefficient
                next_bracket[(letter,) + word] -= coefficient
            bracket = next_bracket
        projected = Counter()
        for word, coefficient in bracket.items():
            exterior = word[:-1]
            if len(set(exterior)) == p - 1:
                parity = sum(exterior[i] > exterior[j]
                             for i in range(len(exterior))
                             for j in range(i + 1, len(exterior)))
                projected[word[-1]] += (-1)**parity * coefficient
        assert set(projected) == {0}
        assert abs(projected[0]) == 3 and projected[0] % p != 0
        coefficients[p] = projected[0]
    return coefficients


if __name__ == "__main__":
    print("Diagonal alignment cases:", check_corner_alignment())
    for p in (3, 5):
        automorphisms, restrictions = check_subgroups(p)
        print(f"Prime {p}: {automorphisms} ambient automorphisms, {restrictions} restrictions.")
    print("Surviving exterior coefficients:", check_exterior_coefficients())
