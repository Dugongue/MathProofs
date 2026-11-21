"""Exact controls for affine recovery and the projective local calculation."""

from itertools import permutations, product
from random import Random


def row_rank(rows, width, prime):
    pivots = {}
    for source in rows:
        row = [value % prime for value in source]
        for index in range(width):
            if not row[index]:
                continue
            if index in pivots:
                scale = row[index]
                row = [(a - scale * b) % prime for a, b in zip(row, pivots[index])]
                continue
            inverse = pow(row[index], -1, prime)
            pivots[index] = [value * inverse % prime for value in row]
            break
    return len(pivots)


def marker_form(data_value):
    """Use the two evaluation coordinates and the marker in each block."""
    triples = {}
    for role in range(3):
        for indices in permutations((3 * role, 3 * role + 1, 3 * role + 2)):
            triples[indices] = 1
    for indices in permutations((0, 3, 6)):
        triples[indices] = data_value
    return triples


def centroid_rows(form, width):
    for i, j, k in product(range(width), repeat=3):
        first = [0] * (width * width)
        second = [0] * (width * width)
        for m in range(width):
            first[m * width + i] += form.get((m, j, k), 0)
            first[m * width + j] -= form.get((i, m, k), 0)
            second[m * width + j] += form.get((i, m, k), 0)
            second[m * width + k] -= form.get((i, j, m), 0)
        yield first
        yield second


def add_product(table, left, right, result, scale):
    table[left, right] = (result, scale)
    table[right, left] = (result, scale)


def carrier_table(form, width):
    size = 2 * width + 2
    table = {(0, i): (i, 1) for i in range(size)}
    table.update({(i, 0): (i, 1) for i in range(size)})
    for i in range(width):
        add_product(table, i + 1, width + i + 1, size - 1, 1)
    for (i, j, k), value in form.items():
        if value:
            assert (i + 1, j + 1) not in table or table[i + 1, j + 1] == (
                width + k + 1, value
            )
            add_product(table, i + 1, j + 1, width + k + 1, value)
    return table


def multiply(table, x, y, modulus):
    result = [0] * len(x)
    for (left, right), (output, value) in table.items():
        result[output] += x[left] * y[right] * value
    return tuple(coefficient % modulus for coefficient in result)


def basis_vector(size, index):
    return tuple(int(i == index) for i in range(size))


def projective_controls(form, width, prime):
    table = carrier_table(form, width)
    size = 2 * width + 2
    basis = [basis_vector(size, j) for j in range(size)]
    socle = basis[-1]
    random = Random(271828)
    points = [socle]
    for _ in range(36):
        data = random.randrange(width)
        primal = basis[data + 1][1:width + 1]
        dual = [random.randrange(prime) for _ in range(width)]
        dual[data] = 0
        points.append((0, *primal, *dual, random.randrange(prime)))
        dual[data] = 1
        points.append((0, *(0,) * width, *dual, random.randrange(prime)))

    for x in points:
        assert not any(multiply(table, x, x, prime))
        jacobian = [multiply(table, x, y, prime) for y in basis]
        assert (row_rank(jacobian, size, prime) == 1) == (x == socle)

    quadratic_parts = [dict() for _ in range(size)]
    for (left, right), (output, value) in table.items():
        left_degree = 2 if left == 0 else int(left != size - 1)
        right_degree = 2 if right == 0 else int(right != size - 1)
        if left_degree + right_degree != 2 or output == size - 1:
            continue
        assert 1 <= left <= width and 1 <= right <= width
        key = tuple(sorted((left - 1, right - 1)))
        quadratic_parts[output][key] = (
            quadratic_parts[output].get(key, 0) + value
        ) % prime
    expected = [dict() for _ in range(size)]
    for (i, j, k), value in form.items():
        if i < j and value:
            expected[width + k + 1][i, j] = 2 * value % prime
    assert quadratic_parts == expected
    return len(points), len(quadratic_parts)


def marker_controls():
    centroid_cases = tangent_cases = quadratic_coordinates = rescaling_cases = 0
    width = 9
    for prime in (3, 5, 7):
        for value in range(prime):
            form = marker_form(value)
            dimension = width * width - row_rank(
                centroid_rows(form, width), width * width, prime
            )
            assert dimension == (1 if value else 3)
            centroid_cases += 1

            tangents, coordinates = projective_controls(form, width, prime)
            tangent_cases += tangents
            quadratic_coordinates += coordinates

            if value:
                multipliers = [(a,) * 3 for a in range(1, prime)]
            else:
                multipliers = product(range(1, prime), repeat=3)
            for a in multipliers:
                scales = [1] * width
                for role in range(3):
                    scales[3 * role + 2] = a[role]
                if value:
                    scales[0] = a[0]
                    scales[1] = pow(a[0], -1, prime)
                for (i, j, k), entry in form.items():
                    assert (
                        scales[i] * scales[j] * scales[k] * entry % prime
                        == a[k // 3] * entry % prime
                    )
                    rescaling_cases += 1
    return centroid_cases, tangent_cases, quadratic_coordinates, rescaling_cases


def affine_ring_controls():
    modulus = 9
    table = {(0, 0): (0, 1), (0, 1): (1, 1), (1, 0): (1, 1)}
    points = list(product(range(modulus), repeat=2))
    basis = [(1, 0), (0, 1)]
    vertex_cases = 0
    unit_cases = 0
    for x in points:
        if not any(multiply(table, x, x, modulus)):
            derivative_zero = all(
                not any(2 * v % modulus for v in multiply(table, x, b, modulus))
                for b in basis
            )
            assert derivative_zero == (x == (0, 0))
            vertex_cases += 1
        for a in points:
            if a[0] % 3 == 0:
                continue
            ax = multiply(table, a, x, modulus)
            expected = multiply(
                table,
                multiply(table, a, a, modulus),
                multiply(table, x, x, modulus),
                modulus,
            )
            assert multiply(table, ax, ax, modulus) == expected
            unit_cases += 1
    return vertex_cases, unit_cases


if __name__ == "__main__":
    print("Centroids, projective tangents, local quadratic coordinates, rescalings:",
          marker_controls())
    print("Square-zero sections and unit-linearization identities over Z/9:",
          affine_ring_controls())
