from itertools import product


CHAIN_STARTS = (0, 2, 5)
CHAIN_LENGTHS = (2, 3, 4)
BASE_DIM = 9
PHASE_DIM = 18
BOTTOMS = (0, 2, 5, 10, 13, 17)


def add(v, w, q):
    return tuple((a + b) % q for a, b in zip(v, w))


def sub(v, w, q):
    return tuple((a - b) % q for a, b in zip(v, w))


def basis_vector(index, dimension):
    return tuple(int(i == index) for i in range(dimension))


def lift_linear(v, q):
    out = [0] * PHASE_DIM
    for start, length in zip(CHAIN_STARTS, CHAIN_LENGTHS):
        for i in range(length):
            ix = start + i
            out[ix] = v[ix]
            if i + 1 < length:
                out[ix] += v[ix + 1]
            out[BASE_DIM + ix] = sum(
                (-1) ** (i - j) * v[BASE_DIM + start + j]
                for j in range(i + 1)
            )
    return tuple(a % q for a in out)


def quadratic(v, q):
    out = [0] * PHASE_DIM
    out[8] = (v[0] * v[2]) % q
    out[9] = (-v[2] * v[17]) % q
    out[11] = (-v[0] * v[17]) % q
    return tuple(out)


def polar(v, w, q):
    return sub(sub(quadratic(add(v, w, q), q), quadratic(v, q), q), quadratic(w, q), q)


def alternating(v, w, q):
    return sum(
        v[i] * w[BASE_DIM + i] - v[BASE_DIM + i] * w[i]
        for i in range(BASE_DIM)
    ) % q


def check_fixed_points(q):
    basis = [basis_vector(i, PHASE_DIM) for i in range(PHASE_DIM)]
    count = 0
    nontrivial = 0
    for bottom_values in product(range(q), repeat=len(BOTTOMS)):
        b_list = [0] * PHASE_DIM
        for i, value in zip(BOTTOMS, bottom_values):
            b_list[i] = value
        b = tuple(b_list)
        assert lift_linear(b, q) == b
        if any(quadratic(b, q)):
            continue
        count += 1
        nonzero_delta = any(any(polar(b, v, q)) for v in basis)
        nontrivial += nonzero_delta

        def derivative(v):
            return lift_linear(add(v, polar(b, v, q), q), q)

        images = [derivative(v) for v in basis]
        assert all(alternating(images[i], images[j], q) == alternating(v, w, q)
                   for i, v in enumerate(basis) for j, w in enumerate(basis))
        fourth_power_nonzero = False
        for v in basis:
            for _ in range(4):
                v = sub(derivative(v), v, q)
            fourth_power_nonzero |= any(v)
        assert nonzero_delta == fourth_power_nonzero
    print(f'F_{q}: all {count} fixed points verified, '
          f'{nontrivial} with nontrivial derivative coupling.')


def check_order(q):
    feature_dimension = BASE_DIM + 6

    def expanded(v):
        x0, x1, y0, y1, y2, z0, z1, z2, z3 = v[:BASE_DIM]
        feature = list(v[BASE_DIM:])
        shifted_features = [0] * 6
        for i, j in product(range(2), range(3)):
            shifted_features[3*i+j] = sum(
                feature[3*a+b]
                for a in range(i, min(i+2, 2))
                for b in range(j, min(j+2, 3))
            )
        return tuple(a % q for a in (
            x0+x1, x1, y0+y1, y1+y2, y2,
            z0+z1, z1+z2, z2+z3, z3+feature[0], *shifted_features
        ))

    basis = [basis_vector(i, feature_dimension) for i in range(feature_dimension)]
    for v in basis:
        for _ in range(8):
            v = sub(expanded(v), v, q)
        assert not any(v)
    bound = q
    while bound < 8:
        bound *= q
    for v in basis:
        image = v
        for _ in range(bound):
            image = expanded(image)
        assert image == v
    print(f'F_{q}: exact augmented linear order divides {bound}.')


if __name__ == '__main__':
    for field in (2, 3):
        check_fixed_points(field)
        check_order(field)
