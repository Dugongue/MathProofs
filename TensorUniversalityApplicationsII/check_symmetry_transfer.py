from itertools import permutations, product
from math import factorial, prod
from random import Random


def label_words(multiplicities):
    labels = tuple(i for i, count in enumerate(multiplicities) for _ in range(count))
    return labels, set(permutations(labels))


def scalar_restriction(tensor, field, maps):
    return sum(coefficient * prod(maps[i][j] for i, j in enumerate(word))
               for word, coefficient in tensor.items()) % field


def check_labels():
    rng = Random(148328)
    checks = 0
    for prime in (2, 3, 5, 7, 11):
        for multiplicities in ((1, 1), (1, 2), (1, 1, 1), (2, 2), (1, 2, 3)):
            labels, words = label_words(multiplicities)
            order = len(labels)
            expected_count = factorial(order) // prod(factorial(x) for x in multiplicities)
            assert len(words) == expected_count
            is_allowed = len(words) % prime != 0
            carries = False
            place = prime
            while place <= order:
                carries |= order // place != sum(x // place for x in multiplicities)
                place *= prime
            assert is_allowed != carries
            if not is_allowed:
                tag = dict.fromkeys(words, 1)
                for coeffs in product(range(prime), repeat=len(multiplicities)):
                    assert scalar_restriction(tag, prime, [coeffs] * order) == 0
                    checks += 1
                selecting = [[int(i == label) for i in range(len(multiplicities))] for label in labels]
                assert scalar_restriction(tag, prime, selecting) == 1
                continue
            words_of_data = tuple(product(range(2), repeat=order))
            for _ in range(13):
                by_weight = [rng.randrange(prime) for _ in range(order + 1)]
                tensor = {word: by_weight[sum(word)] for word in words_of_data}
                maps = [tuple(rng.randrange(prime) for _ in range(2)) for _ in multiplicities]
                expected = scalar_restriction(tensor, prime, [maps[i] for i in labels])
                tagged_terms = [scalar_restriction(tensor, prime, [maps[i] for i in word])
                                for word in words]
                assert all(term == expected for term in tagged_terms)
                assert sum(tagged_terms) * pow(len(words), -1, prime) % prime == expected
                checks += len(words)
    return checks


def f4_mul(a, b):
    output = (a if b & 1 else 0) ^ ((a << 1) if b & 2 else 0)
    if output & 4:
        output ^= 7
    return output


def f4_trace(a):
    return a ^ f4_mul(a, a)


def dual_mul(p, a, b):
    a0, a1 = a
    b0, b1 = b
    return a0*b0 % p, (a1*b0 + a0*b1) % p


def gl_two(p):
    return [matrix for matrix in product(range(p), repeat=4)
            if (matrix[0]*matrix[3] - matrix[1]*matrix[2]) % p]


def tied_form(matrix, form, order, p):
    m = (matrix[:2], matrix[2:])
    result = []
    for word in product(range(2), repeat=order):
        result.append(sum(form[source] * prod(m[word[i]][source[i]] for i in range(order))
                          for source in form) % p)
    return tuple(result)


def check_centroid_examples():
    binary_words = tuple(product(range(2), repeat=3))
    field_forms = [dict((w, f4_trace(f4_mul(a, prod_f4([1 << bit for bit in w]))))
                        for w in binary_words) for a in (1, 2)]
    assert not any(tied_form(m, field_forms[0], 3, 2) == tuple(field_forms[1].values())
                   for m in gl_two(2))

    # Compare all tied isomorphisms of the dual-number cubics in characteristic 3.
    dual_zero = dict((w, int(sum(w) == 1)) for w in binary_words)
    dual_unit = dict((w, int(sum(w) <= 1)) for w in binary_words)
    assert not any(tied_form(m, dual_zero, 3, 3) == tuple(dual_unit.values())
                   for m in gl_two(3))
    assert dual_mul(3, (1, 1), dual_mul(3, (1, 1), (1, 1))) == (1, 0)

    # Check the positive root-extraction branch for every binary invertible matrix at order 5.
    matmul = lambda a, b: tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2)) % 2
                                for i in range(2) for j in range(2))

    def power(a, exponent):
        value = (1, 0, 0, 1)
        for _ in range(exponent):
            value = matmul(value, a)
        return value

    for m in gl_two(2):
        assert power(power(m, 5), 5) == m
    return len(gl_two(2)) * 2 + len(gl_two(3))


def prod_f4(values):
    output = 1
    for x in values:
        output = f4_mul(output, x)
    return output


def check_field_power_supply():
    checks = 0
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        for block in range(1, p):
            powers = {pow(x, block, p) for x in range(p)}
            accumulated = {0}
            for _ in range(block):
                accumulated = {(x + y) % p for x in accumulated for y in powers}
            assert len(accumulated) == p
            checks += 1
    return checks


if __name__ == '__main__':
    print(f'PASS: {check_labels()} exact label comparisons, '
          f'{check_centroid_examples()} finite equalization/isomorphism controls, '
          f'{check_field_power_supply()} prime-field power supply checks')
