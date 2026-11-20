"""Finite checks of scalar descent, pure spans, and prime-power refinements."""

from itertools import product
from math import comb


def row_rank(rows, prime):
    rows = [list(row) for row in rows]
    rank = 0
    for column in range(len(rows[0])):
        pivot = next((i for i in range(rank, len(rows)) if rows[i][column]), None)
        if pivot is None:
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inverse = pow(rows[rank][column], -1, prime)
        rows[rank] = [value * inverse % prime for value in rows[rank]]
        for i in range(rank + 1, len(rows)):
            scale = rows[i][column]
            rows[i] = [
                (left - scale * right) % prime
                for left, right in zip(rows[i], rows[rank])
            ]
        rank += 1
    return rank


def check_pure_spans():
    cases = 0
    for prime in (2, 3, 5, 7, 11):
        for degree in range(1, prime + 5):
            for dimension in (2, 3):
                monomials = [
                    exponent
                    for exponent in product(range(degree + 1), repeat=dimension)
                    if sum(exponent) == degree
                ]
                rows = []
                for point in product(range(prime), repeat=dimension):
                    row = []
                    for exponent in monomials:
                        value = 1
                        for x, e in zip(point, exponent):
                            value = value * pow(x, e, prime) % prime
                        row.append(value)
                    rows.append(row)
                assert (row_rank(rows, prime) == len(monomials)) == (degree <= prime)
                cases += 1
    return cases


def add_f9(x, y):
    return ((x[0] + y[0]) % 3, (x[1] + y[1]) % 3)


def mul_f9(x, y):
    return ((x[0] * y[0] - x[1] * y[1]) % 3, (x[0] * y[1] + x[1] * y[0]) % 3)


def check_quadratic_extension_descent():
    elements = list(product(range(3), repeat=2))
    vectors = list(product(elements, repeat=2))
    alpha = (0, 1)
    minus_one = (2, 0)
    cases = 0
    for x, y in product(vectors, repeat=2):
        descended_s = add_f9(mul_f9(x[0], y[0]), mul_f9(minus_one, mul_f9(x[1], y[1])))[0]
        descended_t = add_f9(mul_f9(x[0], y[0]), mul_f9(mul_f9(alpha, x[1]), mul_f9(alpha, y[1])))[0]
        assert descended_s == descended_t
        cases += 1
    return cases


def multinomial(counts):
    remaining = sum(counts)
    value = 1
    for count in counts:
        value *= comb(remaining, count)
        remaining -= count
    return value


def refine(d, split, prime, labels):
    bins = []
    chunk_size = 1
    quotients = [d - split, split]
    while any(quotients):
        chunks = bins
        new_quotients = []
        for color, quotient in enumerate(quotients):
            next_digit, multiplicity = divmod(quotient, prime)
            chunks.extend([[color] * chunk_size] * multiplicity)
            new_quotients.append(next_digit)
        if not any(new_quotients):
            bins = chunks
            break
        assert len(chunks) % prime == 0
        bins = [sum(chunks[i : i + prime], []) for i in range(0, len(chunks), prime)]
        chunk_size *= prime
        quotients = new_quotients
    assert len(bins) == prime
    counts = [[0] * prime for _ in range(2)]
    for label, entries in zip(labels, bins):
        for color in entries:
            counts[color][label] += 1
    return counts


def check_prime_power_refinements():
    cases = 0
    for prime, max_exponent in ((2, 8), (3, 5), (5, 3), (7, 3)):
        for exponent in range(1, max_exponent + 1):
            d = prime**exponent
            block = d // prime
            label_words = [tuple(range(prime)), (0,) * prime]
            label_words.extend((0,) * i + (1,) * (prime - i) for i in range(1, prime))
            for split in range(1, d):
                for labels in label_words:
                    x_counts, y_counts = refine(d, split, prime, labels)
                    assert sum(x_counts) == d - split
                    assert sum(y_counts) == split
                    assert all(x_counts[i] + y_counts[i] == labels.count(i) * block for i in range(prime))
                    assert multinomial(x_counts) * multinomial(y_counts) % prime
                    cases += 1
    return cases


def check_cyclic_isotropy():
    cases = 0
    for prime in (2, 3, 5):
        for order in range(2, 5):
            multiplicity_rows = []
            for positions in product(range(prime), repeat=order):
                multiplicity_rows.append(tuple(positions.count(i) for i in range(prime)))
            for coefficients in product(range(prime), repeat=order + 1):
                value = 0
                for multiplicities in multiplicity_rows:
                    entry = 1
                    for multiplicity in multiplicities:
                        entry *= coefficients[multiplicity]
                    value += entry
                assert value % prime == 0
                cases += 1
    return cases


def main():
    print(f"pure-span cases: {check_pure_spans()}")
    print(f"quadratic extension descent cases: {check_quadratic_extension_descent()}")
    print(f"prime-power refinements: {check_prime_power_refinements()}")
    print(f"cyclic isotropy cases: {check_cyclic_isotropy()}")


if __name__ == "__main__":
    main()
