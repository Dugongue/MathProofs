"""Exhaustive checks of reciprocal-tensor spans over small finite fields."""

from itertools import product


def remainder(value, modulus, prime):
    work = value.copy()
    for top in range(len(work) - 1, len(modulus) - 2, -1):
        factor = work[top] % prime
        for i, coefficient in enumerate(modulus):
            offset = top - len(modulus) + 1 + i
            work[offset] = (work[offset] - coefficient * factor) % prime
    return work[:len(modulus) - 1]


def find_modulus(prime, degree):
    divisors = [
        [*coefficients, 1]
        for d in range(1, degree // 2 + 1)
        for coefficients in product(range(prime), repeat=d)
    ]
    for coefficients in product(range(prime), repeat=degree):
        candidate = [*coefficients, 1]
        if all(any(remainder(candidate, divisor, prime)) for divisor in divisors):
            return candidate
    raise AssertionError("No irreducible polynomial found")


def multiply(a, b, modulus, prime):
    full = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            full[i + j] = (full[i + j] + ai * bj) % prime
    return remainder(full, modulus, prime)


def power(a, exponent, modulus, prime):
    result = [1] + [0] * (len(a) - 1)
    while exponent:
        if exponent % 2:
            result = multiply(result, a, modulus, prime)
        a = multiply(a, a, modulus, prime)
        exponent //= 2
    return result


def add_row(basis, row, prime):
    for pivot in range(len(row)):
        coefficient = row[pivot]
        if not coefficient:
            continue
        existing = basis.get(pivot)
        if existing is None:
            inverse = pow(coefficient, -1, prime)
            basis[pivot] = [x * inverse % prime for x in row]
            return
        row = [(x - coefficient * y) % prime for x, y in zip(row, existing)]


fields = 0
tensors = 0
for p in (2, 3, 5, 7):
    for s in range(1, 6 if p <= 3 else 4):
        poly = find_modulus(p, s)
        basis = {}
        for a in product(range(p), repeat=s):
            if not any(a):
                continue
            inverse = power(a, p**s - 2, poly, p)
            assert multiply(a, inverse, poly, p) == [1] + [0] * (s - 1)
            add_row(basis, [x * y % p for x in a for y in inverse], p)
            tensors += 1
        assert len(basis) == s*s - s + 1
        fields += 1

print(f"Exact inversion and span dimension for {tensors} tensors over {fields} finite fields.")
