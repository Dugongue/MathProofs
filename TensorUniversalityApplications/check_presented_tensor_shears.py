"""Finite controls for the cover lift and the three coevaluation shears."""

from functools import lru_cache
from itertools import product
from math import gcd
from random import Random


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def multiply(left, right, modulus):
    return [[sum(a * b for a, b in zip(row, column)) % modulus
             for column in zip(*right)] for row in left]


def invertible_matrix(size, modulus, rng):
    direct = identity(size)
    inverse = identity(size)
    if size == 1:
        return direct, inverse
    for _ in range(5):
        row, column = rng.sample(range(size), 2)
        entry = rng.randrange(modulus)
        shear = identity(size)
        shear[row][column] = entry
        direct = multiply(shear, direct, modulus)
        shear[row][column] = -entry
        inverse = multiply(inverse, shear, modulus)
    assert multiply(direct, inverse, modulus) == identity(size)
    return direct, inverse


def kronecker(first, second):
    return [[a * b for a in first_row for b in second_row]
            for first_row in first for second_row in second]


def entries(sizes):
    return product(*(range(size) for size in sizes))


def coevaluation_tensor(array, sizes):
    encoded = dict(array)
    for mode in range(3):
        other = [i for i in range(3) if i != mode]
        for slot, pair in enumerate(entries([sizes[i] for i in other])):
            index = [0, 0, 0]
            index[mode] = sizes[mode] + slot
            for position, value in zip(other, pair):
                index[position] = value
            encoded[tuple(index)] = 1
    return encoded


def transport(tensor, maps, modulus):
    supports = [[[(i, row[j]) for i, row in enumerate(matrix) if row[j] % modulus]
                 for j in range(len(matrix[0]))] for matrix in maps]
    result = {}
    for (i, j, k), coefficient in tensor.items():
        if not coefficient:
            continue
        for (a, u), (b, v), (c, w) in product(supports[0][i], supports[1][j], supports[2][k]):
            key = (a, b, c)
            result[key] = (result.get(key, 0) + coefficient * u * v * w) % modulus
    return {index: coefficient for index, coefficient in result.items() if coefficient}


@lru_cache(maxsize=None)
def residual_ideal(modulus, generators):
    terms = [[(r * d) % modulus for r in range(modulus)] for d in generators]
    return {sum(scalars) % modulus for scalars in product(*terms)}


def check_sector_identity(modulus, sizes, rng):
    matrix_pairs = [invertible_matrix(size, modulus, rng) for size in sizes]
    direct, inverse = tuple(zip(*matrix_pairs))
    divisors = [d for d in range(1, modulus + 1) if modulus % d == 0]
    kernel_diagonal = [[rng.choice(divisors) for _ in range(size)] for size in sizes]
    original = {index: rng.randrange(modulus) for index in entries(sizes)}
    residual_before_basis_change = dict.fromkeys(entries(sizes), 0)
    block_maps = []
    for mode in range(3):
        j, k = [index for index in range(3) if index != mode]
        complement = sizes[j] * sizes[k]
        inverse_tensor = kronecker(inverse[j], inverse[k])
        dual_inverse = list(map(list, zip(*inverse_tensor)))
        coordinate_shear = [[d * rng.randrange(modulus) % modulus for _ in range(complement)]
                            for d in kernel_diagonal[mode]]
        shear = multiply(direct[mode], coordinate_shear, modulus)
        block_maps.append([row + tail for row, tail in zip(direct[mode], shear)]
                          + [[0] * sizes[mode] + row for row in dual_inverse])
        for index in entries(sizes):
            slot = index[j] * sizes[k] + index[k]
            residual_before_basis_change[index] += coordinate_shear[index[mode]][slot]

    changed_array = transport({index: (value + residual_before_basis_change[index]) % modulus
                               for index, value in original.items()}, direct, modulus)
    encoded = coevaluation_tensor(original, sizes)
    predicted = {index: value for index, value in coevaluation_tensor(changed_array, sizes).items() if value}
    assert transport(encoded, block_maps, modulus) == predicted

    membership_checks = 0
    for index in entries(sizes):
        ideals = tuple(sorted(kernel_diagonal[mode][index[mode]] for mode in range(3)))
        common = gcd(*ideals)
        attainable = residual_ideal(modulus, ideals)
        for residue in range(modulus):
            assert (residue in attainable) == (residue % common == 0)
            membership_checks += 1
        assert residual_before_basis_change[index] % common == 0
    return membership_checks


def check_stable_lift():
    # Different integral presentations onto Z/6. The target first-coordinate
    # map (z0,z1) -> 4*z0+3*z1 represents multiplication by 5 on the quotient.
    def into_target(x):
        return (2 * x, x)

    def into_source(y):
        return 2 * y[0] + 3 * y[1]

    checks = 0
    for x, y0, y1 in product(range(-4, 5), repeat=3):
        w = x - into_source((y0, y1))
        displacement = into_target(w)
        z = (y0 + displacement[0], y1 + displacement[1])
        assert (4 * z[0] + 3 * z[1] - 5 * x) % 6 == 0
        recovered_y = (z[0] - displacement[0], z[1] - displacement[1])
        recovered_x = w + into_source(recovered_y)
        assert (recovered_x, *recovered_y) == (x, y0, y1)
        checks += 1
    return checks


def main():
    rng = Random(7403)
    sector_checks = 0
    membership_checks = 0
    for modulus in (2, 4, 6, 8, 9, 12):
        for _ in range(48):
            sizes = tuple(rng.randrange(1, 4) for _ in range(3))
            membership_checks += check_sector_identity(modulus, sizes, rng)
            sector_checks += 1
    print(f'{check_stable_lift()} integral cover lifts, {sector_checks} exact sector identities, '
          f'{membership_checks} residue membership checks passed')


if __name__ == '__main__':
    main()
