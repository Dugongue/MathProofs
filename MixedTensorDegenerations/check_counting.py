"""Finite controls for exact rank-marker and presented-tensor transporter counts."""

from collections import Counter
from itertools import product
from math import prod


def zero(rows, columns):
    return tuple((0,) * columns for _ in range(rows))


def identity(size):
    return tuple(tuple(int(i == j) for j in range(size)) for i in range(size))


def rows_of(size, columns, modulus):
    for entries in product(range(modulus), repeat=size * columns):
        yield tuple(entries[i:i + columns] for i in range(0, len(entries), columns))


def transpose(matrix):
    return tuple(zip(*matrix))


def multiply(first, second, modulus):
    columns = tuple(zip(*second))
    return tuple(tuple(sum(x * y for x, y in zip(row, col)) % modulus
                       for col in columns) for row in first)


def determinant(matrix, modulus):
    size = len(matrix)
    if size == 1:
        return matrix[0][0] % modulus
    minors = (
        tuple(row[:index] + row[index + 1:] for row in matrix[1:])
        for index in range(size)
    )
    return sum((-1)**i * entry * determinant(minor, modulus)
               for i, (entry, minor) in enumerate(zip(matrix[0], minors))) % modulus


def matrix_rank(matrix, prime):
    work = [list(row) for row in matrix]
    pivot = 0
    for column in range(len(work[0])):
        candidates = (i for i in range(pivot, len(work)) if work[i][column] % prime)
        row_id = next(candidates, None)
        if row_id is None:
            continue
        work[pivot], work[row_id] = work[row_id], work[pivot]
        pivot_row = work[pivot]
        inverse = pow(pivot_row[column], -1, prime)
        for row in work[pivot + 1:]:
            factor = row[column] * inverse
            for j, value in enumerate(pivot_row):
                row[j] = (row[j] - factor * value) % prime
        pivot += 1
    return pivot


def gl_order(size, prime, length=1):
    return prime**((length - 1) * size * size) * prod(
        prime**size - prime**i for i in range(size)
    )


def glue(*sectors):
    return tuple(sum(row_blocks, ()) for block_row in sectors for row_blocks in zip(*block_row))


def embed_rows(matrix, row_count):
    return matrix + zero(row_count - len(matrix), len(matrix[0]))


def marker_control(prime, a, a_i, b, w, b_zero, slice_count, c_zero, nonzero):
    """Enumerate all block candidates allowed by slice support, then test raw equality."""
    inclusion = embed_rows(identity(a_i), a)
    marker = glue(
        (zero(a, b), inclusion, zero(a, w)),
        (identity(b), zero(b, a_i), zero(b, w)),
        (zero(w, b), zero(w, a_i), identity(w)),
    )
    # Each retained Z_0 coordinate can carry a nonconstant old slice.
    old_slices = [
        tuple(tuple(int(nonzero and (i + 2*j + index) % 3 == 0) for j in range(b))
              for i in range(a))
        for index in range(slice_count)
    ]
    old_shifts = []
    for coordinates in product(range(prime), repeat=c_zero):
        old_shifts.append(tuple(
            tuple(sum(value * old_slices[k][i][j] for k, value in enumerate(coordinates)) % prime
                  if i < a and j < b else 0 for j in range(b + a_i + w))
            for i in range(a + b + w)
        ))
    invertible = {
        n: [matrix for matrix in rows_of(n, n, prime) if determinant(matrix, prime)]
        for n in {a_i, b, w}
    }
    # Right blocks are generated independently of any marker equation.
    left_choices = []
    for upper_l, upper_r, lower, diagonal_l, diagonal_r in product(
        rows_of(a, b, prime), rows_of(a, w, prime), rows_of(w, b, prime),
        invertible[b], invertible[w],
    ):
        p = glue(
            (identity(a), upper_l, upper_r),
            (zero(b, a), diagonal_l, zero(b, w)),
            (zero(w, a), lower, diagonal_r),
        )
        left_choices.append(multiply(p, marker, prime))
    right_choices = []
    for upper_m, upper_s, lower, diagonal_m, diagonal_s in product(
        rows_of(b_zero, a_i, prime), rows_of(b_zero, w, prime), rows_of(w, a_i, prime),
        invertible[a_i], invertible[w],
    ):
        q = glue(
            (identity(b), embed_rows(upper_m, b), embed_rows(upper_s, b)),
            (zero(a_i, b), diagonal_m, zero(a_i, w)),
            (zero(w, b), lower, diagonal_s),
        )
        right_choices.append(transpose(q))
    target = Counter(
        tuple(tuple((entry - change) * pow(scale, -1, prime) % prime
                    for entry, change in zip(row, shift))
              for row, shift in zip(marker, old_shift))
        for scale in range(1, prime)
        for old_shift in old_shifts
    )
    observed = sum(target[multiply(left, right, prime)]
                   for left in left_choices for right in right_choices)
    expected = (prime - 1) * gl_order(w, prime) * prime**(
        w * a_i + (a_i + w) * b_zero + c_zero
    )
    assert observed == expected, (observed, expected)
    return observed


def original_rank_bands(prime, copies):
    """Build the actual published marker weights and check all covectors."""
    a, b = 2, 1
    marked_blocks = [0] * copies + [1] * copies
    k = len(marked_blocks)
    weights = [(k + i + 2) * (a + b + 1) for i in range(k)]
    # Old two-dimensional X support intentionally has dimension only one.
    row_count = a + k + sum(weights)
    column_count = b + k + sum(weights)
    row_starts = [a + k + sum(weights[:i]) for i in range(k)]
    column_starts = [b + k + sum(weights[:i]) for i in range(k)]
    for values in product(range(prime), repeat=k+1):
        old, *coefficients = values
        # Delete unused private rows/columns while keeping each active identity,
        # whose pivots are disjoint from every other block.
        matrix = [[0] * (b+k) for _ in range(a+k)]
        matrix[0][0] = old
        private_pivots = set()
        for i, (coefficient, marked) in enumerate(zip(coefficients, marked_blocks)):
            matrix[marked][b+i] = coefficient
            matrix[a+i][0] = coefficient
            if coefficient:
                private_pivots.update(
                    (row_starts[i]+off, column_starts[i]+off) for off in range(weights[i])
                )
        assert all(i < row_count and j < column_count for i, j in private_pivots)
        rank = len(private_pivots) + matrix_rank(matrix, prime)
        active = [i for i, coefficient in enumerate(coefficients) if coefficient]
        assert (rank <= a+b) == (not active)
        for i, weight in enumerate(weights):
            assert (weight <= rank <= weight+a+b) == (active == [i])


def cover_factor(prime, length, cyclic_lengths):
    modulus = prime**length
    r = len(cyclic_lengths)
    minimum_rank = sum(d > 0 for d in cyclic_lengths)
    t = r - minimum_rank
    module_size = prime**sum(cyclic_lengths)
    return (modulus**minimum_rank // module_size)**r * modulus**(t*minimum_rank) * gl_order(
        t, prime, length
    )


def cover_control(prime, length, cyclic_lengths, quotient_scale=None):
    modulus = prime**length
    r = len(cyclic_lengths)
    if quotient_scale is None:
        quotient_scale = (1,) * r
    observed = 0
    for matrix in rows_of(r, r, modulus):
        if determinant(matrix, prime) == 0:
            continue
        if all((entry - (quotient_scale[i] if i == j else 0)) % prime**cyclic_lengths[i] == 0
               for i, row in enumerate(matrix) for j, entry in enumerate(row)):
            observed += 1
    assert observed == cover_factor(prime, length, cyclic_lengths)
    return observed


def tensor_transform(coefficients, maps, modulus):
    dimensions = tuple(len(matrix) for matrix in maps)
    indices = tuple(product(*(range(size) for size in dimensions)))
    return tuple(
        sum(value * prod(maps[i][target[i]][source[i]] for i in range(3))
            for source, value in zip(indices, coefficients)) % modulus
        for target in indices
    )


def shear_control(prime, length, cyclic_lengths, maps):
    modulus = prime**length
    f = tuple(len(section) for section in cyclic_lengths)
    indices = tuple(product(*(range(size) for size in f)))
    axis_periods = [tuple(prime**e for e in section) for section in cyclic_lengths]
    sector_sets = []
    for i in range(3):
        coordinate_choices = (
            range(0, modulus, axis_periods[i][index[i]]) for index in indices
        )
        acted_maps = tuple(identity(f[j]) if j == i else maps[j] for j in range(3))
        sector_sets.append([
            tensor_transform(coefficients, acted_maps, modulus)
            for coefficients in product(*coordinate_choices)
        ])
    observed = Counter(
        tuple(sum(entries) % modulus for entries in zip(*choices))
        for choices in product(*sector_sets)
    )
    correct_image = set(product(*(
        range(0, modulus, min(axis_periods[i][index[i]] for i in range(3)))
        for index in indices
    )))
    assert set(observed) == correct_image
    quotient_size = prime**sum(
        min(cyclic_lengths[i][index[i]] for i in range(3)) for index in indices
    )
    image_size = modulus**prod(f) // quotient_size
    kernel_sizes = tuple(modulus**f[i] // prime**sum(cyclic_lengths[i]) for i in range(3))
    expected = prod(kernel_sizes[i]**prod(f[j] for j in range(3) if j != i)
                    for i in range(3)) // image_size
    assert len(observed) == image_size
    assert set(observed.values()) == {expected}
    return image_size, expected


def free_marked_control(prime, length, cyclic_lengths, first, second):
    """Compare explicit tensor movers with quotient movers for rank-one covers."""
    modulus = prime**length
    vectors = tuple(product(range(modulus), repeat=2))
    first_mark = {(x, 0) for x in range(modulus)}
    marked_maps = []
    for cyclic_length in cyclic_lengths:
        second_mark = {point for point in vectors if point[0] % prime**cyclic_length == 0}
        good = []
        for matrix in rows_of(2, 2, modulus):
            if determinant(matrix, prime) == 0:
                continue
            def image(submodule):
                return {tuple(sum(a*b for a, b in zip(row, vector)) % modulus for row in matrix)
                        for vector in submodule}
            if image(first_mark) == first_mark and image(second_mark) == second_mark:
                good.append(matrix)
        marked_maps.append(good)
    binary_indices = tuple(product(range(2), repeat=3))
    def with_coevaluations(value):
        return tuple(value if sum(index) == 0 else int(sum(index) == 1)
                     for index in binary_indices)
    target = with_coevaluations(second)
    observed = sum(tensor_transform(with_coevaluations(first), maps, modulus) == target
                   for maps in product(*marked_maps))
    quotient_modulus = prime**min(cyclic_lengths)
    units = [tuple(x for x in range(prime**e) if x % prime) if e else (1,)
             for e in cyclic_lengths]
    quotient_count = sum((first * prod(scalars) - second) % quotient_modulus == 0
                         for scalars in product(*units))
    cover_count = prod(cover_factor(prime, length, (e,)) for e in cyclic_lengths)
    shear_count = prod(modulus // prime**e for e in cyclic_lengths) * quotient_modulus // modulus
    assert observed == quotient_count * cover_count * shear_count
    return quotient_count, observed


def algebra_control(modulus, prime):
    """Enumerate all automorphisms of a two-vertex triangular algebra independently."""
    coordinates = tuple(product(range(modulus), repeat=3))
    basis = identity(3)
    unit = (1, 1, 0)
    def algebra_product(first, second):
        x, y, z = first
        r, s, t = second
        return x*r % modulus, y*s % modulus, (x*t + z*s) % modulus
    def acted(columns, vector):
        return tuple(sum(value*column[i] for value, column in zip(vector, columns)) % modulus
                     for i in range(3))
    autos = []
    for first, arrow in product(coordinates, repeat=2):
        second = tuple((u-a) % modulus for u, a in zip(unit, first))
        columns = (first, second, arrow)
        if determinant(columns, prime) and all(
            acted(columns, algebra_product(a, b)) == algebra_product(
                acted(columns, a), acted(columns, b)
            ) for a, b in product(basis, repeat=2)
        ):
            autos.append(columns)
    units = [z for z in coordinates if z[0] % prime and z[1] % prime]
    assert len(autos) == modulus * (modulus - modulus//prime)
    independent_units = (modulus - modulus//prime)**2 * modulus
    assert len(units) == independent_units
    isotopies = set()
    for columns, left, right in product(autos, units, units):
        first = tuple(algebra_product(left, image) for image in columns)
        second = tuple(algebra_product(image, right) for image in columns)
        output = tuple(algebra_product(image, right) for image in first)
        assert all(
            acted(output, algebra_product(a, b)) == algebra_product(
                acted(first, a), acted(second, b)
            ) for a, b in product(basis, repeat=2)
        )
        isotopies.add((first, second, output))
    assert len(isotopies) == len(autos) * independent_units**2
    return len(autos), len(isotopies)


def main():
    marker_examples = (
        (2, 2, 1, 1, 1, 1, 1, 1, False),
        (2, 2, 1, 2, 1, 1, 2, 1, True),
        (2, 1, 1, 1, 2, 1, 2, 2, True),
        (3, 1, 1, 1, 1, 1, 1, 1, True),
    )
    print("exhaustive individual marker fibers", [marker_control(*row) for row in marker_examples])
    original_rank_bands(2, 1)
    original_rank_bands(3, 2)
    print("original weight bands, single and doubled marker layouts")

    cover_examples = [
        (2, 2, (1, 0), None), (2, 3, (2, 0), (3, 1)),
        (3, 2, (1, 1), (2, 1)), (2, 1, (1, 0, 0), None),
        (2, 2, (0, 0), None), (2, 2, (2, 2), None),
    ]
    print("exhaustive free-cover fibers", [cover_control(*row) for row in cover_examples])

    shear_examples = [
        (2, 2, ((1,), (1,), (2,)), (((1,),), ((1,),), ((1,),))),
        (2, 2, ((1, 0), (1,), (2,)), (((1, 2), (1, 1)), ((1,),), ((3,),))),
        (2, 3, ((1,), (2,), (3,)), (((3,),), ((5,),), ((7,),))),
        (3, 2, ((1,), (1,), (2,)), (((2,),), ((4,),), ((8,),))),
    ]
    print("shear images and fibers", [shear_control(*row) for row in shear_examples])
    print("quotient and marked tensor counts", [
        free_marked_control(2, 2, (1, 1, 2), x, y)
        for x, y in [(1, 3), (0, 2), (0, 1)]
    ])
    print("two-vertex algebra automorphisms and checked isotopies", algebra_control(4, 2))


if __name__ == "__main__":
    main()
