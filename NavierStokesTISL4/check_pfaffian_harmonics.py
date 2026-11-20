"""Exact controls for the ternary Fourier readout and the relation color lock."""

from itertools import product
from random import Random


def field_vectors(size):
    yield from product(range(3), repeat=size)


def dot(left, right):
    return sum(a * b for a, b in zip(left, right, strict=True)) % 3


def sign(value):
    return (0, 1, -1)[value % 3]


def kernel(rows, width):
    reduced = [list(row) for row in rows]
    pivots = []
    for j in range(width):
        i = len(pivots)
        choice = next((a for a in range(i, len(reduced)) if reduced[a][j]), None)
        if choice is None:
            continue
        reduced[i], reduced[choice] = reduced[choice], reduced[i]
        inverse = reduced[i][j]
        reduced[i] = [entry * inverse % 3 for entry in reduced[i]]
        for a, row in enumerate(reduced):
            if a != i and row[j]:
                factor = row[j]
                reduced[a] = [(x - factor * y) % 3 for x, y in zip(row, reduced[i], strict=True)]
        pivots.append(j)
    free = [j for j in range(width) if j not in pivots]
    for j in free:
        vector = [0] * width
        vector[j] = 1
        for i, pivot in enumerate(pivots):
            vector[pivot] = -reduced[i][j] % 3
        yield tuple(vector)


def linear_combinations(rows, width):
    for coeffs in field_vectors(len(rows)):
        yield tuple(sum(k * row[j] for k, row in zip(coeffs, rows, strict=True)) % 3
                    for j in range(width))


def primal_imbalance(factors, multiplicities, label_dimension, coeff=1):
    total = 0
    for label in field_vectors(label_dimension):
        value = coeff
        for factor, exponent in zip(factors, multiplicities, strict=True):
            value = value * pow(dot(factor, label), exponent, 3) % 3
        total += sign(value)
    return total


def dual_imbalance(relations, multiplicities, label_dimension, coeff=1):
    n = len(multiplicities)
    odd = sum(exponent % 2 for exponent in multiplicities)
    if odd % 2:
        return 0
    total = 0
    for relation in linear_combinations(relations, n):
        weight = sign(coeff)
        for exponent, coordinate in zip(multiplicities, relation, strict=True):
            if exponent % 2:
                weight *= sign(coordinate)
            else:
                weight *= 2 if coordinate == 0 else -1
        total += weight
    divisor = 3 ** n
    numerator = total * 3 ** label_dimension * (-3) ** (odd // 2)
    assert numerator % divisor == 0
    return numerator // divisor


def tag(relations, exponents, coeff=1):
    color = coeff
    for j, exponent in enumerate(exponents):
        if not exponent % 2:
            continue
        first = next((row[j] for row in relations if row[j]), None)
        if first is None:
            return None
        color = color * first % 3
    return color


def pfaffian(matrix):
    a = [row[:] for row in matrix]
    size = len(a)
    result = 1
    for i in range(0, size, 2):
        j = next((j for j in range(i+1, size) if a[i][j]), None)
        if j is None:
            return 0
        if j != i + 1:
            a[i+1], a[j] = a[j], a[i+1]
            for row in a:
                row[i+1], row[j] = row[j], row[i+1]
            result = -result
        pivot = a[i][i+1]
        result = result * pivot % 3
        for s in range(i+2, size):
            for t in range(s+1, size):
                change = (a[i][s] * a[i+1][t] - a[i][t] * a[i+1][s]) * pivot
                a[s][t] = (a[s][t] - change) % 3
                a[t][s] = -a[s][t] % 3
    return result % 3


def pencil_pfaffian(diagonal, rng):
    n = len(diagonal)
    matrix = [[0] * (2*n) for _ in range(2*n)]
    expected = (-1) ** (n * (n-1)//2)
    for i, value in enumerate(diagonal):
        matrix[i][n+i] = value
        matrix[n+i][i] = -value % 3
        expected = expected * value % 3
        for j in range(i+1, n):
            entry = rng.randrange(3)
            matrix[n+i][n+j] = entry
            matrix[n+j][n+i] = -entry % 3
    assert pfaffian(matrix) == expected
    return expected


def checks():
    rng = Random(0x3FCA)
    for _ in range(240):
        dims = rng.randint(1, 4)
        raw = {vector for vector in field_vectors(dims) if any(vector)}
        normalized = sorted({tuple(next(x for x in v if x)*entry % 3 for entry in v) for v in raw})
        factors = rng.sample(normalized, rng.randint(1, min(len(normalized), 8)))
        exponents = [rng.randint(1, 4) for _ in factors]
        coeff = rng.choice((1, 2))
        rels = list(kernel(list(zip(*factors, strict=True)), len(factors)))
        assert primal_imbalance(factors, exponents, dims, coeff) == dual_imbalance(rels, exponents, dims, coeff)

    for m in range(1, 33):
        b = 2 * m
        n = 3 * b
        relations = [(1,) * b + (0,) * b + (1,) * b, (0,) * b + (1,) * b + (1,) * b]
        vectors = list(linear_combinations(relations, n))
        assert sorted(sum(c != 0 for c in vector) for vector in vectors) == [0] + [2*b]*6 + [3*b]*2
        assert dual_imbalance(relations, [1]*n, n-2) == 2 * (-3)**(3*m) // 9
        if m == 1:
            primal_basis = list(kernel(relations, n))
            factors = list(zip(*primal_basis, strict=True))
            assert primal_imbalance(factors, [1]*n, n-2) == 2 * (-3)**(3*m) // 9

    colors = 0
    for b in range(3, 66, 2):
        n = 4 * b
        r0 = (1,) * b + (0,) * b + (1,) * (2*b)
        r1 = (0,) * b + (1,) * (2*b) + (2,) * b
        vectors = list(linear_combinations([r0,r1], n))
        assert dual_imbalance([r0,r1], [1]*n, n-2) == 0
        assert all(tag([v], [1]*n) is None for v in vectors)
        good = [(r,s) for r,s in product(vectors, repeat=2) if tag([r,s], [1]*n) is not None]
        assert len(good) == 48
        index_map = [i if i < 2*b else i+b if i<3*b else i-b for i in range(n)]
        scales = (2,)*b + (1,)*b + (2,)*(2*b)
        def transform(vector):
            result = [0] * n
            for i, value in enumerate(vector):
                result[index_map[i]] = value * scales[i] % 3
            return tuple(result)
        assert all(transform(v) in vectors for v in vectors)
        for r,s in good:
            assert tag([transform(r),transform(s)], [1]*n) == -tag([r,s], [1]*n) % 3
            colors += 1

    for n in range(2, 17):
        for _ in range(12):
            pencil_pfaffian([rng.randrange(3) for _ in range(n)], rng)
            pencil_pfaffian([rng.choice((1, 2)) for _ in range(n)], rng)
    return "240 primal/dual controls, 32 large-circuit means, {} odd color flips, 360 raw block Pfaffians".format(colors)



def permutation_sign(images):
    seen = set()
    result = 1
    for value in images:
        if value in seen:
            continue
        length = 0
        while value not in seen:
            seen.add(value)
            value = images[value]
            length += 1
        if length % 2 == 0:
            result = -result
    return result


def normalize_vector(vector):
    scale = next(x for x in vector if x)
    return tuple(x * scale % 3 for x in vector), sign(scale)


def matrix_vector(matrix, vector):
    return tuple(dot(row, vector) for row in matrix)


def invertible_matrix(dimension, rng):
    matrix = [[int(i == j) for j in range(dimension)] for i in range(dimension)]
    determinant = 1
    for _ in range(3 * dimension):
        i, j = rng.sample(range(dimension), 2)
        choice = rng.randrange(3)
        if choice == 0:
            matrix[i], matrix[j] = matrix[j], matrix[i]
            determinant = -determinant
        elif choice == 1:
            matrix[i] = [-x % 3 for x in matrix[i]]
            determinant = -determinant
        else:
            matrix[i] = [(a + b) % 3 for a,b in zip(matrix[i], matrix[j],strict=True)]
    return matrix, determinant


def projective_controls():
    rng = Random(0xD027)
    checked = 0
    for dimension in range(2, 8):
        points = [vector for vector in field_vectors(dimension) if any(vector)]
        lines = sorted({normalize_vector(v)[0] for v in points})
        point_ids = {point: i for i, point in enumerate(points)}
        line_ids = {line: i for i, line in enumerate(lines)}
        for _ in range(12):
            matrix, determinant = invertible_matrix(dimension, rng)
            point_perm = [point_ids[matrix_vector(matrix, v)] for v in points]
            assert permutation_sign(point_perm) == determinant
            raw_images = [normalize_vector(matrix_vector(matrix, v)) for v in lines]
            line_perm = [line_ids[v] for v, _ in raw_images]
            assert permutation_sign(line_perm) == determinant ** (dimension - 1)
            line_scale = 1
            for _, factor in raw_images:
                line_scale *= factor
            assert line_scale == determinant

            x_order, y_order = list(range(len(lines))), list(range(len(lines)))
            rng.shuffle(x_order)
            rng.shuffle(y_order)
            y_indices = {direction: i for i, direction in enumerate(y_order)}
            x_signs = [rng.choice((1,-1)) for _ in lines]
            y_signs = [rng.choice((1,-1)) for _ in lines]
            sigma = [y_indices[line_perm[i]] for i in x_order]
            observed_product, x_calibration, y_calibration = 1, 1, 1
            for j,i in enumerate(x_order):
                factor = x_signs[j] * raw_images[i][1] * y_signs[sigma[j]]
                observed_product *= factor
                x_calibration *= x_signs[j]
                y_calibration *= y_signs[j]
            assert observed_product == x_calibration * y_calibration * determinant
            assert permutation_sign(sigma) == (permutation_sign(x_order) * permutation_sign(y_order)
                                               * determinant ** (dimension - 1))
            checked += 1
    return checked

if __name__ == '__main__':
    assert __debug__
    print(checks())
    print(f"{projective_controls()} complete projective frequency actions with endpoint calibration")
