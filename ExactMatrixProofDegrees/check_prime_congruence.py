"""Exhaust small congruence orbits with independent length-one and length-two signs."""

from itertools import product


def gram(rows, pairing, prime):
    return tuple(pairing(x, y) % prime for x in rows for y in rows)


def verify_length_two():
    for prime in (3, 5, 7, 11):
        vectors = list(product(range(prime), repeat=2))
        def pairing(x, y):
            return x[0] * y[1] - x[1] * y[0] + x[1] * y[1]
        orbit = {gram(rows, pairing, prime) for rows in product(vectors, repeat=2)}
        for scale in range(1, prime):
            target = (0, scale, -scale % prime, scale)
            assert (target in orbit) == (pow(scale, (prime - 1) // 2, prime) == 1)


def verify_two_lengths():
    prime = 3
    vectors = list(product(range(prime), repeat=3))
    def pairing(x, y):
        return x[0] * y[0] + x[1] * y[2] - x[2] * y[1] + x[2] * y[2]
    orbit = {gram(rows, pairing, prime) for rows in product(vectors, repeat=3)}
    for first, second in product((1, 2), repeat=2):
        target = (first, 0, 0, 0, 0, second, 0, -second % prime, second)
        assert (target in orbit) == (first == second == 1)


if __name__ == "__main__":
    verify_length_two()
    verify_two_lengths()
    print("Verified all nonzero scales at four primes and four joint signatures in dimension three.")
