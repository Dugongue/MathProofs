"""Exact binary controls for crossed-flattening tensor factor recovery."""
from random import Random


def bits(word):
    while word:
        low = word & -word
        yield low.bit_length() - 1
        word ^= low


def identity(size):
    return [1 << row for row in range(size)]


def transpose(mat, columns):
    result = [0] * columns
    for row, mask in enumerate(mat):
        for col in bits(mask):
            result[col] |= 1 << row
    return result


def product(left, right):
    result = []
    for row in left:
        total = 0
        for j in bits(row):
            total ^= right[j]
        result.append(total)
    return result


def inverse(mat):
    size = len(mat)
    rows = [v | (1 << (size + i)) for i, v in enumerate(mat)]
    for j in range(size):
        pivot = next((i for i in range(j, size) if rows[i] & (1 << j)), None)
        if pivot is None:
            return None
        rows[j], rows[pivot] = rows[pivot], rows[j]
        for i in range(size):
            if i != j and rows[i] & (1 << j):
                rows[i] ^= rows[j]
    return [word >> size for word in rows]


def partial_transpose(mat, a, b):
    result = [0] * (a * b)
    for row, mask in enumerate(mat):
        i, j = divmod(row, b)
        for col in bits(mask):
            k, ell = divmod(col, b)
            result[i * b + ell] |= 1 << (k * b + j)
    return result


def marginals(mat, a, b):
    first = [0] * a
    second = [0] * b
    for row, mask in enumerate(mat):
        i, j = divmod(row, b)
        for col in bits(mask):
            k, ell = divmod(col, b)
            if j == ell:
                first[i] ^= 1 << k
            if i == k:
                second[j] ^= 1 << ell
    return first, second


def portraits(mat, a, b):
    inverse_cross = inverse(partial_transpose(mat, a, b))
    if inverse_cross is None or inverse(mat) is None:
        return None
    mixed = product(mat, partial_transpose(inverse_cross, a, b))
    assert marginals(mixed, a, b) == (
        identity(a) if b & 1 else [0] * a,
        identity(b) if a & 1 else [0] * b,
    )
    delta = [m ^ v for m, v in zip(mixed, identity(a * b))]
    delta2 = product(delta, delta)
    delta3 = product(delta2, delta)
    return tuple(zip(marginals(delta2, a, b), marginals(delta3, a, b)))


def intertwiners(src, dst):
    """Basis of the space of X with X A = B X for both given pairs (A,B)."""
    size = len(src[0])
    pivots = {}
    for orig, target in zip(src, dst):
        for i in range(size):
            for j in range(size):
                row = 0
                for k in range(size):
                    if (orig[k] >> j) & 1:
                        row ^= 1 << (i * size + k)
                    if (target[i] >> k) & 1:
                        row ^= 1 << (k * size + j)
                while row:
                    pivot = row.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = row
                        break
                    row ^= pivots[pivot]
    mask = (1 << size) - 1
    basis = []
    for free in range(size * size):
        if free not in pivots:
            vec = 1 << free
            for pivot in sorted(pivots):
                if (pivots[pivot] & vec).bit_count() % 2:
                    vec |= 1 << pivot
            basis.append([(vec >> (i * size)) & mask for i in range(size)])
    return basis


def kronecker(left, right):
    return [
        sum(r << (j * len(right)) for j in bits(left_row))
        for left_row in left for r in right
    ]


def factor_kronecker(mat, a, b):
    small_right_mask = (1 << b) - 1
    right = None
    left = [0] * a
    for i in range(a):
        for k in range(a):
            block = [(mat[i * b + j] >> (k * b)) & small_right_mask for j in range(b)]
            if any(block):
                if right is None:
                    right = block
                if right != block:
                    return None
                left[i] |= 1 << k
    return (left, right) if right is not None else None


def transporter(src, dst, a, b):
    orig, target = portraits(src, a, b), portraits(dst, a, b)
    if orig is None or target is None:
        return None
    factors = []
    for source_pair, target_pair in zip(orig, target):
        basis = intertwiners(source_pair, target_pair)
        if len(basis) != 1 or inverse(basis[0]) is None:
            return None
        factors.append(basis[0])
    left = kronecker(*factors)
    right_t = product(product(inverse(src), inverse(left)), dst)
    rf = factor_kronecker(transpose(right_t, a * b), a, b)
    if rf is None:
        return None
    assert product(product(left, src), transpose(kronecker(*rf), a * b)) == dst
    return tuple(factors) + rf


def random_mat(rng, size):
    return [rng.getrandbits(size) for _ in range(size)]


def random_gl(rng, size):
    while True:
        mat = random_mat(rng, size)
        if inverse(mat) is not None:
            return mat


def verify():
    rng = Random(20261115)
    count = 0
    for a, b in [(3, 3), (4, 4), (5, 5), (6, 6), (8, 8), (3, 7)]:
        invertible = solved = 0
        for _ in range(200):
            raw = random_mat(rng, a * b)
            value = portraits(raw, a, b)
            if value is None:
                continue
            invertible += 1
            if any(len(intertwiners(pair, pair)) != 1 for pair in value):
                continue
            solved += 1
            if solved <= 5:
                hidden = tuple(random_gl(rng, d) for d in (a, b, a, b))
                scrambled = product(
                    product(kronecker(*hidden[:2]), raw),
                    transpose(kronecker(*hidden[2:]), a * b),
                )
                assert transporter(raw, scrambled, a, b) == hidden
                count += 1
        assert solved >= 5
        print(f'{a}x{b}x{a}x{b}: {solved}/{invertible} accepted among invertible cut pairs, 200 draws.')
    print(f'{count} exact constructive recoveries verified over F2.')


if __name__ == '__main__':
    verify()
