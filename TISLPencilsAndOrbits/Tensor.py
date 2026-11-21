"""Exhaustive characteristic-three controls for the slice-algebra profiles."""

from itertools import product


Q = 3
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 1)


def transpose(matrix):
    a, b, c, d = matrix
    return a, c, b, d


def det(matrix):
    a, b, c, d = matrix
    return (a * d - b * c) % Q


def add(first, second):
    return tuple((a + b) % Q for a, b in zip(first, second))


def scale(matrix, scalar):
    return tuple(x * scalar % Q for x in matrix)


def multiply(first, second):
    a, b, c, d = first
    e, f, g, h = second
    return ((a * e + b * g) % Q, (a * f + b * h) % Q,
            (c * e + d * g) % Q, (c * f + d * h) % Q)


def determinant_profiles(slices, invertible):
    coordinates = {
        add(scale(slices[0], a), scale(slices[1], b)): (a, b)
        for a, b in product(range(Q), repeat=2)
    }
    profile = set()
    for left, right in product(invertible, repeat=2):
        images = [multiply(multiply(left, item), transpose(right)) for item in slices]
        if any(image not in coordinates for image in images):
            continue
        first, second = [coordinates[image] for image in images]
        third_det = pow(det(first + second), -1, Q)
        profile.add((det(left), det(right), third_det))
    return profile


def check_recovery(matrices):
    # An invertible left translate of the split diagonal algebra, with singular slices.
    slices = ((0, 0, 1, 0), (0, 1, 0, 0))
    assert all(det(slice_) == 0 for slice_ in slices)
    endomorphisms = []
    for left, right in product(matrices, repeat=2):
        if all(multiply(left, item) == multiply(item, right) for item in slices):
            endomorphisms.append((left, right))
    center = [
        (left, right) for left, right in endomorphisms
        if all(multiply(left, a) == multiply(a, left)
               and multiply(right, b) == multiply(b, right)
               for a, b in endomorphisms)
    ]
    assert len(center) == 9
    central_idempotents = [
        (left, right) for left, right in center
        if multiply(left, left) == left and multiply(right, right) == right
    ]
    nontrivial = [item for item in central_idempotents if item not in ((ZERO, ZERO), (ONE, ONE))]
    assert len(nontrivial) == 2
    result = ZERO
    for left, right in nontrivial:
        projected = [multiply(left, item) for item in slices]
        assert projected == [multiply(item, right) for item in slices]
        nonzero = [item for item in projected if item != ZERO]
        assert len(nonzero) == 1
        result = add(result, nonzero[0])
    assert result == (0, 1, 1, 0) and det(result)
    return len(matrices) ** 2


matrices = list(product(range(Q), repeat=4))
invertible = [matrix for matrix in matrices if det(matrix)]
assert len(invertible) == 48
nilpotent = determinant_profiles((ONE, (0, 1, 0, 0)), invertible)
assert nilpotent == {(1, 1, 1), (2, 2, 2)}
split = determinant_profiles(((1, 0, 0, 0), (0, 0, 0, 1)), invertible)
assert split == set(product((1, 2), repeat=3))
count = check_recovery(matrices)
print(f"Checked {2 * len(invertible)**2} stabilizer candidates and {count} endomorphism pairs over F3.")
print("Determinant profiles had sizes 2 (truncated algebra) and 8 (split diagonal algebra).")
