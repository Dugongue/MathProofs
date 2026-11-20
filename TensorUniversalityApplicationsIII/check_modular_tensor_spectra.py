"""Exact finite controls for prime-order compensation and Frobenius collapse."""

from itertools import permutations, product
from math import factorial, prod
from random import Random


def compensation(prime, width):
    # Start with (e_1 + ... + e_width)^tensor prime.
    coefficients = {word: 1 for word in product(range(width), repeat=prime)}
    label_words = tuple(permutations(range(prime)))
    for new_index in range(1, width):
        for multiplicity in range(1, prime):
            divisor = factorial(multiplicity) * factorial(prime - multiplicity)
            scale = -pow(divisor, -1, prime)
            images = [range(new_index)] * (prime - multiplicity)
            images += [(new_index,)] * multiplicity
            for labels in label_words:
                for word in product(*(images[label] for label in labels)):
                    coefficients[word] += scale
    for word, value in coefficients.items():
        assert value % prime == int(len(set(word)) == 1)
    return len(coefficients)


def transform_entry(coefficients, input_words, rows, prime):
    return sum(coefficients[word] * prod(row[index] for row, index in zip(rows, word))
               for word in input_words) % prime


def frobenius_collapse(prime, extra, rng):
    # F4 and F9 lift the test beyond x^p == x as functions on the ground field.
    degree = 2
    size = prime**degree
    polynomial = (1, 1) if prime == 2 else (1, 0)
    digits = [(a % prime, a // prime) for a in range(size)]

    def add(a, b):
        a0, a1 = digits[a]
        b0, b1 = digits[b]
        return (a0+b0) % prime + prime * ((a1+b1) % prime)

    def multiply(a, b):
        a0, a1 = digits[a]
        b0, b1 = digits[b]
        high = a1 * b1
        return ((a0*b0 - polynomial[0]*high) % prime
                + prime * ((a0*b1+a1*b0-polynomial[1]*high) % prime))

    def power(a):
        b = 1
        for _ in range(prime):
            b = multiply(a, b)
        return b

    def transformed(table, words, rows):
        answer = 0
        for word in words:
            value = table[word]
            for row, index in zip(rows, word):
                value = multiply(value, row[index])
            answer = add(answer, value)
        return answer

    n = 2
    order = prime + extra
    original_words = tuple(product(range(n), repeat=order))
    reduced_words = tuple(product(range(n), repeat=extra+1))
    classes = {tuple(sorted(w[:prime])) + w[prime:] for w in original_words}
    values = {c: rng.randrange(size) for c in sorted(classes)}
    coefficients = {w: values[tuple(sorted(w[:prime])) + w[prime:]] for w in original_words}
    reduced = {w: coefficients[(w[0],)*prime + w[1:]] for w in reduced_words}
    rows = [tuple(rng.randrange(size) for _ in range(n)) for _ in range(3)]
    remaining = [[tuple(rng.randrange(size) for _ in range(n)) for _ in range(2)]
                 for _ in range(extra)]
    for output_index in product(range(3), *[range(2) for _ in range(extra)]):
        head = rows[output_index[0]]
        tail = [matrix[i] for matrix, i in zip(remaining, output_index[1:])]
        left = transformed(coefficients, original_words, [head]*prime + tail)
        right = transformed(reduced, reduced_words, [tuple(map(power, head))] + tail)
        assert left == right
    return 3 * 2**extra


def visible_binary(prime):
    checks = 0
    binary_words = tuple(product(range(2), repeat=prime))
    vectors = tuple(product(range(prime), repeat=2))
    for by_weight in product(range(prime), repeat=prime+1):
        x_coeff, y_coeff = by_weight[0], by_weight[-1]
        if x_coeff == y_coeff == 0:
            continue
        pure = tuple(x_coeff**(prime-j) * y_coeff**j % prime for j in range(prime+1))
        if by_weight == pure:
            continue
        coefficients = {w: by_weight[sum(w)] for w in binary_words}
        scout = [v for v in vectors if (v[0]*x_coeff+v[1]*y_coeff) % prime == 1]
        zero_pairs = []
        for j in range(1, prime):
            one_pair = next(((x, y) for x, y in product(scout, repeat=2)
                             if transform_entry(coefficients, binary_words,
                                                (x,)*(prime-j)+(y,)*j, prime) == 0), None)
            assert one_pair is not None
            zero_pairs.append(one_pair)
        letters = tuple(product(range(2), repeat=prime-1))
        power_words = tuple(product(range(len(letters)), repeat=prime))
        powered = {}
        for word in power_words:
            columns = [letters[i] for i in word]
            powered[word] = prod(coefficients[column] for column in zip(*columns)) % prime
        rows = [tuple(prod(zero_pairs[i][r][index] for i, index in enumerate(w)) % prime
                      for w in letters) for r in range(2)]
        for word in binary_words:
            value = transform_entry(powered, power_words, [rows[r] for r in word], prime)
            assert value == int(len(set(word)) == 1)
            checks += 1
    return checks


def finite_field_power_example():
    prime = 5
    words = tuple(product(range(2), repeat=prime))
    tensor = {word: int(sum(word) in (0, 4)) for word in words}
    for s, t in product(range(prime), repeat=2):
        expected = (1 + 3*s**2*t**2 + 2*s**3*t) % prime
        observed = transform_entry(tensor, words, [(1, s)]*3 + [(1, t)]*2, prime)
        assert observed == expected != 0
    x = (1, 1)
    e = ((1, 0), (0, 1))
    contraction = tuple(tuple(transform_entry(tensor, words, [x]*3+[u, v], prime)
                              for v in e) for u in e)
    assert contraction == ((1, 1), (1, 3))
    row = (1, 0, 2, 1)
    positions = tuple(product(range(2), repeat=2))
    second_power_value = sum(row[a] * row[b] * contraction[i][j] * contraction[k][l]
                             for a, (i, k) in enumerate(positions)
                             for b, (j, l) in enumerate(positions))
    assert row[0] == 1 and second_power_value % prime == 0


if __name__ == "__main__":
    compensation_count = sum(compensation(prime, width)
                             for prime in (2, 3, 5)
                             for width in (2, 3, 4))
    rng = Random(289)
    collapse_count = sum(frobenius_collapse(prime, extra, rng)
                         for prime in (2, 3)
                         for extra in range(3)
                         for _ in range(20))
    extractor_count = sum(visible_binary(prime) for prime in (2, 3))
    finite_field_power_example()
    print(f"PASS: {compensation_count} compensation coefficients, "
          f"{collapse_count} extension-field collapse checks, "
          f"{extractor_count} exact extractor coefficients, and the F5 power example")
