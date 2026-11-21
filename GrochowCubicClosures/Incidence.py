"""Finite checks for the cubic Grassmannian incidence calculations."""

from itertools import combinations, product


def multiply(left, right):
    """Multiply in F_3[t]/(t^m), with m given by the tuple length."""
    length = len(left)
    coefficients = [0] * length
    for i, a in enumerate(left):
        for j in range(length - i):
            coefficients[i + j] = (coefficients[i + j] + a * right[j]) % 3
    return tuple(coefficients)


def check_artinian_graphs():
    total, allowed = 0, 0
    for length in range(1, 7):
        cube_zero = 0
        for value in product(range(3), repeat=length):
            cube = multiply(value, multiply(value, value))
            assert (not any(cube)) == (not any(value[:(length + 2) // 3]))
            cube_zero += not any(cube)
            total += 1
        assert cube_zero == 3 ** (length - (length + 2) // 3)
        allowed += cube_zero
    return total, allowed


def check_common_monomials():
    total = 0
    for dimension in range(1, 7):
        all_monomials = set(product(range(3), repeat=dimension))
        for rank in range(dimension + 1):
            intersection = set(all_monomials)
            for plane in combinations(range(dimension), rank):
                monomials = {monomial for monomial in all_monomials
                             if all(not exponent or axis in plane
                                    for axis, exponent in enumerate(monomial))}
                assert len(monomials) == 3 ** rank
                intersection &= monomials
                total += 1
            expected = all_monomials if rank == dimension else {(0,) * dimension}
            assert intersection == expected
    return total


def check_projective_line_cech():
    # The degree-j generator on the second chart is t**(-j) times the first.
    # Over the overlap, regular sections from the two charts contribute
    # monomial exponents >= 0 and <= -j, respectively.
    supports = []
    for degree in range(3):
        first = {power for power in range(-4, 5) if power >= 0}
        second = {power for power in range(-4, 5) if power <= -degree}
        h_zero = first & second
        h_one = set(range(-4, 5)) - first - second
        supports.append((sorted(h_zero), sorted(h_one)))
    assert supports == [([0], []), ([], []), ([], [-1])]
    return supports


def matrix_rank(matrix):
    rows = [list(row) for row in matrix]
    pivot_row = 0
    for column in range(len(rows[0])):
        index = next((i for i in range(pivot_row, len(rows)) if rows[i][column]), None)
        if index is None:
            continue
        rows[pivot_row], rows[index] = rows[index], rows[pivot_row]
        pivot = rows[pivot_row]
        pivot_inverse = pivot[column]
        for i in range(pivot_row + 1, len(rows)):
            scalar = rows[i][column] * pivot_inverse
            rows[i] = [(left - scalar * right) % 3 for left, right in zip(rows[i], pivot)]
        pivot_row += 1
    return pivot_row


def check_ternary_polarizations():
    triples = [standard for standard in product(range(4), repeat=3)
               if sum(standard) == 3 and 3 not in standard]
    assert len(triples) == 7
    counts = [0] * 4
    for coefficients in product(range(3), repeat=7):
        form = dict(zip(triples, coefficients))
        matrix = []
        for i in range(3):
            row = []
            for j, k in product(range(3), repeat=2):
                exponent = tuple((i == e) + (j == e) + (k == e) for e in range(3))
                weight = 2 if 2 in exponent else 1
                row.append(weight * form.get(exponent, 0) % 3)
            matrix.append(row)
        counts[matrix_rank(matrix)] += 1
    assert counts[0] == 1 and counts[1] == 0 and sum(counts) == 2187
    return counts


if __name__ == "__main__":
    print("Artinian graph coordinates tested and admitted:", check_artinian_graphs())
    print("Coordinate Grassmannian planes tested:", check_common_monomials())
    print("Cech supports in degrees 0, 1, and 2:", check_projective_line_cech())
    print("Ternary polarization counts by rank:", check_ternary_polarizations())
