from collections import Counter
from itertools import product


q = 3
matrices = list(product(range(q), repeat=4))


def det(m):
    return (m[0] * m[3] - m[1] * m[2]) % q


invertible = [m for m in matrices if det(m)]


def multiply(a, b):
    return tuple(
        sum(a[2 * i + k] * b[2 * k + j] for k in range(2)) % q
        for i in range(2) for j in range(2)
    )


def diagonal_tensor_fibers():
    result = Counter()
    for a, b, c in product(invertible, repeat=3):
        valid = True
        for i, j, k in product(range(2), repeat=3):
            value = sum(a[2 * i + s] * b[2 * j + s] * c[2 * k + s]
                        for s in range(2)) % q
            if value != int(i == j == k):
                valid = False
                break
        if valid:
            result[(det(a), det(b), det(c))] += 1
    return result


def ordered_tuple_fibers(slices):
    result = Counter()
    for p, r in product(invertible, repeat=2):
        if all(multiply(p, m) == multiply(m, r) for m in slices):
            result[(det(p), pow(det(r), -1, q))] += 1
    return result


if __name__ == "__main__":
    fibers = diagonal_tensor_fibers()
    assert fibers == {d: 4 for d in product((1, 2), repeat=3)}
    print("Two equal scalar tensor blocks: all eight determinant fibers have size four.")

    identity = (1, 0, 0, 1)
    nilpotent = (0, 1, 0, 0)
    irreducible = (0, 2, 1, 0)
    assert ordered_tuple_fibers([identity]) == {(1, 1): 24, (2, 2): 24}
    assert ordered_tuple_fibers([identity, nilpotent]) == {(1, 1): 6}
    assert ordered_tuple_fibers([identity, irreducible]) == {(1, 1): 4, (2, 2): 4}
    print("Ordered tuples: exact split matrix, nonreduced local, and quadratic-field fibers.")
