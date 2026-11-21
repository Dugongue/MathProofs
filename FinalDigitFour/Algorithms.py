"""Exact controls for the final-digit orbit quotient."""

from itertools import product
from random import Random


def add(x, y, modulus):
    return tuple((a + b) % modulus for a, b in zip(x, y))


def difference(x, y, modulus):
    return tuple((a - b) % modulus for a, b in zip(x, y))


def eye(n):
    return tuple(tuple(int(i == j) for j in range(n)) for i in range(n))


def columns_to_matrix(columns):
    return tuple(zip(*columns))


def mat_vec(matrix, vector, modulus):
    return tuple(sum(a * b for a, b in zip(row, vector)) % modulus for row in matrix)


def linear_combination(coefficients, vectors, modulus):
    return tuple(sum(a * b for a, b in zip(coefficients, column)) % modulus
                 for column in zip(*vectors))


def evaluate(tensor, x, y, modulus):
    slices = [linear_combination(y, row, modulus) for row in tensor]
    return linear_combination(x, slices, modulus)


def change_basis(tensor, left_inverse, right_inverse, output, modulus):
    left = tuple(zip(*left_inverse))
    right = tuple(zip(*right_inverse))
    return tuple(tuple(mat_vec(output, evaluate(tensor, x, y, modulus), modulus)
                       for y in right) for x in left)


def anchor(size):
    basis = eye(size)
    zero = (0,) * size
    return tuple(tuple(basis[j] if i == 0 else basis[i] if j == 0 else zero
                       for j in range(size)) for i in range(size))


def first_order_columns(size, p):
    base = anchor(size)
    for mode, a, b in product(range(3), range(size), range(size)):
        coefficients = []
        for i, j, r in product(range(size), repeat=3):
            if mode == 0:
                value = -int(i == b) * base[a][j][r]
            elif mode == 1:
                value = -int(j == b) * base[i][a][r]
            else:
                value = int(r == a) * base[i][j][b]
            coefficients.append(value % p)
        yield coefficients


def rank(vectors, p):
    pivots = {}
    for vector in vectors:
        vector = list(vector)
        for index in range(len(vector)):
            entry = vector[index]
            if entry == 0:
                continue
            if index in pivots:
                vector = [(a - entry * b) % p for a, b in zip(vector, pivots[index])]
            else:
                inverse = pow(entry, -1, p)
                pivots[index] = tuple(a * inverse % p for a in vector)
                break
    return len(pivots)


def near_inverse(matrix, modulus):
    return tuple(tuple((2 * int(i == j) - value) % modulus for j, value in enumerate(row))
                 for i, row in enumerate(matrix))


def normalize(tensor, p):
    n = len(tensor)
    modulus = p * p
    identity = eye(n)
    left_inv = near_inverse(columns_to_matrix(tuple(tensor[i][0] for i in range(n))), modulus)
    right_inv = near_inverse(columns_to_matrix(tensor[0]), modulus)
    unital = change_basis(tensor, left_inv, right_inv, identity, modulus)
    frame = columns_to_matrix((tensor[0][0], *identity[1:]))
    unital = change_basis(unital, frame, frame, near_inverse(frame, modulus), modulus)
    assert unital[0] == identity
    assert tuple(row[0] for row in unital) == identity
    pos = [2 if i == 1 else 1 for i in range(1, n)]
    ell = tuple(unital[i][j][j] // p for i, j in enumerate(pos, 1))
    shift = [list(row) for row in identity]
    for i, value in enumerate(ell, 1):
        shift[0][i] = -p * value
    result = change_basis(unital, shift, shift, near_inverse(shift, modulus), modulus)
    assert all(result[i][j][j] == 0 for i, j in enumerate(pos, 1))
    return result


def random_k(rng, n, p):
    return tuple(tuple(int(i == j) + p * rng.randrange(p) for j in range(n)) for i in range(n))


def check_quotient(n, p, samples, rng):
    base = anchor(n)
    assert rank(first_order_columns(n, p), p) == 2 * n * n - 1
    for _ in range(samples):
        tensor = tuple(tuple(tuple(x + p * rng.randrange(p) for x in value)
                             for value in row) for row in base)
        a, b, c = [random_k(rng, n, p) for _ in range(3)]
        moved = change_basis(tensor, near_inverse(a, p * p), near_inverse(b, p * p), c, p * p)
        canonical = normalize(tensor, p)
        assert normalize(moved, p) == canonical == normalize(canonical, p)
    print(f"p={p}, N={n}: rank {2*n*n-1}, {samples} orbit normalization checks")


def check_no_trace(p, e):
    # The only radical product is e1*e2 = p**(e-1) e3.
    # Here N=4 and p=2 divides N. Exhaust every residue matrix and augmentation row.
    n, modulus, s = 3, p ** e, p ** (e - 1)
    basis = eye(n)
    all_vectors = tuple(product(range(p), repeat=n))
    invertible = (columns for columns in product(all_vectors, repeat=n) if rank(columns, p) == n)
    cases, successes = 0, 0
    for cols in invertible:
        for augmentations in product(range(0, modulus, p), repeat=n):
            cases += 1
            ok = True
            for i, j in product(range(n), repeat=2):
                actual = tuple(
                    (augmentations[i] * cols[j][r] + augmentations[j] * cols[i][r]
                     + (s * cols[i][0] * cols[j][1] if r == 2 else 0)) % modulus
                    for r in range(n)
                )
                wanted = tuple(s * x % modulus for x in cols[2]) if (i, j) == (0, 1) else (0,) * n
                if actual != wanted or augmentations[i] * augmentations[j] % modulus:
                    ok = False
                    break
            if ok:
                assert augmentations == (0,) * n
                successes += 1
    assert successes == (p - 1) ** 2 * p ** 2
    print(f"p={p}, e={e}, N=4: {cases} augmentation tests, {successes} residual automorphisms")


def check_rank_one_count():
    vectors = tuple(product(range(2), repeat=3))
    pairs = ((l, r) for l in vectors[1:] for r in vectors[1:] if l != r)
    encoded = set()
    for l, r in pairs:
        for v in vectors[1:]:
            if sum(x * y for x, y in zip(l, v)) % 2 or sum(x * y for x, y in zip(r, v)) % 2:
                continue
            encoded.add(tuple(l[i] * r[j] * v[k] for i, j, k in product(range(3), repeat=3)))
    assert len(encoded) == 42
    print("p=2, N=4: 42 labeled supported rank-(1,1,1) tensors")


if __name__ == "__main__":
    rng = Random(39)
    for n, p in ((3, 2), (4, 2), (3, 3), (4, 3)):
        check_quotient(n, p, 32, rng)
    check_no_trace(2, 2)
    check_no_trace(2, 3)
    check_rank_one_count()
