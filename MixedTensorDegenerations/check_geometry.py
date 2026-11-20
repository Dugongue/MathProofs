"""Exact finite controls for selected identities in the degeneration proof."""

from itertools import product


def matrix_product(left, right):
    return tuple(
        tuple(sum(a * b for a, b in zip(row, column)) % 4
              for column in zip(*right))
        for row in left
    )


def transpose(matrix):
    return tuple(zip(*matrix))


def inverse_transpose(matrix):
    (a, b), (c, d) = matrix
    det = (a * d - b * c) % 4
    if det % 2 == 0:
        return None
    return ((det * d % 4, -det * c % 4),
            (-det * b % 4, det * a % 4))


def scale(matrix, unit):
    return tuple(tuple(unit * entry % 4 for entry in row) for row in matrix)


def gauge_replay():
    names = ("primal", "dual")
    identity = ((1, 0), (0, 1))
    repeated = ((1, 2), (0, 3))
    nilpotent_map = ((0, 1), (0, 0))
    zero = ((0, 0), (0, 0))
    words = (
        ((), ((2,),)),
        (("primal", "primal"), repeated),
        (("primal", "dual"), nilpotent_map),
        (("primal", "dual"), identity),
        (("dual", "dual"), zero),
    )
    count = 0
    for a11, a12, a21, a22 in product(range(4), repeat=4):
        primal = ((a11, a12), (a21, a22))
        dual = inverse_transpose(primal)
        if dual is None:
            continue
        assert matrix_product(primal, transpose(dual)) == identity
        intended = dict(zip(names, (primal, dual)))
        for tag_a, tag_b, pad, r_primal, r_dual in product((1, 3), repeat=5):
            returns = dict(zip(names, (r_primal, r_dual)))
            outgoing = {
                name: scale(intended[name], pad * returns[name])
                for name in names
            }
            prefix_length = 2
            marker_count = len(words)
            reference = pow(pad, prefix_length, 4) * tag_b * pow(tag_a, marker_count, 4) % 4
            for index, (word, payload) in enumerate(words, start=1):
                tag = pow(tag_a, index, 4) * tag_b * pow(tag_a, marker_count - index, 4) % 4
                path_weight = pow(pad, prefix_length - len(word), 4) * tag
                for name in word:
                    path_weight *= returns[name]
                normalized_weight = path_weight * pow(reference, -1, 4) % 4
                if word:
                    observed = matrix_product(
                        matrix_product(outgoing[word[0]], payload),
                        transpose(outgoing[word[1]]),
                    )
                    expected = matrix_product(
                        matrix_product(intended[word[0]], payload),
                        transpose(intended[word[1]]),
                    )
                else:
                    observed = expected = payload
                assert scale(observed, normalized_weight) == expected
            count += 1
    assert count == 3072
    return count


def noncommutative_isotope_replay():
    # Upper triangular 2-by-2 matrices over F_3, stored as (top-left, off-diagonal, bottom-right).
    def mul(x, y):
        a, b, c = x
        d, e, f = y
        return a * d % 3, (a * e + b * f) % 3, c * f % 3

    a, a_inverse = (2, 0, 1), (2, 0, 1)
    b, b_inverse = (1, 1, 1), (1, 2, 1)
    assert mul(a, b) != mul(b, a)
    unit = mul(a, b)
    identity = (1, 0, 1)

    def m(x, y):
        return mul(mul(a, mul(x, y)), b)

    def inverse_slice(x):
        return mul(mul(a_inverse, x), b_inverse)

    def normalized(x, y):
        return m(inverse_slice(x), inverse_slice(y))

    assert m(identity, identity) == unit
    matrices = tuple(product(range(3), repeat=3))
    for x, y in product(matrices, repeat=2):
        assert normalized(mul(unit, x), mul(unit, y)) == mul(unit, mul(x, y))
    return len(matrices) ** 2


if __name__ == "__main__":
    print("Tagged graded gauges over Z/4:", gauge_replay())
    print("Noncommutative isotope normalization pairs over F_3:", noncommutative_isotope_replay())

