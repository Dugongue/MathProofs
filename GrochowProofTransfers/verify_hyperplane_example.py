"""Exhaustive check of the two-label rank certificate for normalized 2x2 pencils over F_3."""
from itertools import product

Q = 3
ZERO = (0, 0, 0, 0)
IDENTITY = (1, 0, 0, 1)
BASIS = ((1, 0, 0), (0, 1, 0), (0, 0, 1))
SEPARATOR = BASIS[0]


def scale(scalar, matrix):
    return tuple(scalar * value % Q for value in matrix)


def add(left, right):
    return tuple((a + b) % Q for a, b in zip(left, right))


def determinant(matrix):
    a, b, c, d = matrix
    return (a * d - b * c) % Q


def product_matrix(left, right):
    a, b, c, d = left
    e, f, g, h = right
    return tuple(value % Q for value in (a * e + b * g, a * f + b * h,
                                         c * e + d * g, c * f + d * h))


def nullity(matrix):
    if matrix == ZERO:
        return 2
    return int(determinant(matrix) == 0)


def evaluate(slices, point):
    matrix = ZERO
    for scalar, term in zip(point, slices):
        matrix = add(matrix, scale(scalar, term))
    return matrix


def determinant_is_xy(slices):
    if any(determinant(matrix) for matrix in slices):
        return False
    first, second, third = slices
    # With all square coefficients zero, these are exactly the mixed coefficients.
    return tuple(determinant(add(a, b)) for a, b in
                 ((first, second), (first, third), (second, third))) == (1, 0, 0)


def sampled_points(direction):
    # w + t v for the two labels x and y. The single collision is at t = y - x.
    collision = (direction[1] - direction[0]) % Q
    regular = (collision + 1) % Q
    return (SEPARATOR,
            tuple((x + collision * v) % Q for x, v in zip(direction, SEPARATOR)),
            tuple((x + regular * v) % Q for x, v in zip(direction, SEPARATOR)))


def rank_certificate(slices):
    for direction in BASIS:
        for point in sampled_points(direction):
            matrix = evaluate(slices, point)
            labels = point[:2]
            for label in set(labels):
                shifted = add(matrix, scale(-label, IDENTITY))
                if nullity(shifted) != labels.count(label):
                    return False
    return True


def projector_certificate(slices):
    first, second, third = slices
    # If B=xP+y(I-P), normalized at (1,1,0), then P is B(1,0,0).
    return (third == ZERO and product_matrix(first, first) == first
            and nullity(first) == 1 and add(first, second) == IDENTITY)


def main():
    total = split = accepted = 0
    matrices = tuple(product(range(Q), repeat=4))
    for first, third in product(matrices, repeat=2):
        total += 1
        second = add(IDENTITY, scale(-1, first))
        slices = first, second, third
        by_rank = rank_certificate(slices)
        if not determinant_is_xy(slices):
            assert not by_rank, slices
            continue
        split += 1
        by_projector = projector_certificate(slices)
        assert by_rank == by_projector, slices
        accepted += by_rank
    assert (total, split, accepted) == (6561, 60, 12)
    print(f"F_{Q}: {total} normalized pencils, {split} determinant-xy pencils, "
          f"{accepted} accepted by both criteria.")


if __name__ == "__main__":
    main()
