"""Independently check the nine-point construction over F_4."""

from itertools import permutations, product


def multiply(a, b):
    result = 0
    while b:
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 4:
            a ^= 7
    return result


def conjugate(a):
    return multiply(a, a)


def scale(a, v):
    return tuple(multiply(a, x) for x in v)


def add(u, v):
    return tuple(x ^ y for x, y in zip(u, v, strict=True))


def normalize(v):
    return scale(conjugate(next(x for x in v if x)), v)


def combine(columns, coefficients):
    result = (0, 0, 0, 0)
    for column, coefficient in zip(columns, coefficients, strict=True):
        result = add(result, scale(coefficient, column))
    return result


BASIS = tuple(tuple(int(i == j) for i in range(4)) for j in range(4))
POINTS = BASIS + ((1, 2, 0, 0), (0, 1, 3, 0), (0, 0, 1, 1),
                  (1, 0, 0, 1), (1, 1, 1, 1))
MARKED = set(POINTS)
COEFFICIENTS = tuple(product(range(4), repeat=4))


def outer(v):
    return tuple(multiply(a, conjugate(b)) for a in v for b in v)


def check_rank_one_locus():
    span = {(0,) * 16}
    for v in POINTS:
        span |= {add(matrix, outer(v)) for matrix in span}
    assert len(span) == 512
    projective = {normalize(v) for v in COEFFICIENTS if any(v)}
    assert len(projective) == 85
    assert {v for v in projective if outer(v) in span} == MARKED


def check_no_frobenius_stabilizer():
    # An image of the four basis points and the all-ones point fixes a
    # projectivity. Frobenius fixes those five source points.
    inverse_trials = tuple(product(range(1, 4), repeat=4))
    tested_frames = 0
    for trial in permutations(POINTS, 5):
        images, last = trial[:4], trial[4]
        if len({combine(images, cs) for cs in COEFFICIENTS}) != 256:
            continue
        coefficients = next((cs for cs in inverse_trials
                             if combine(images, cs) == last), None)
        if coefficients is None:
            continue
        tested_frames += 1
        columns = tuple(scale(c, v) for c, v in zip(coefficients, images, strict=True))
        image_set = {normalize(combine(columns, tuple(map(conjugate, v)))) for v in POINTS}
        assert image_set != MARKED, (trial, columns)
    assert tested_frames > 0
    return tested_frames


if __name__ == "__main__":
    check_rank_one_locus()
    frames = check_no_frobenius_stabilizer()
    print(f"PASS: 85 projective points, 512 span elements, {frames} full frame images.")
