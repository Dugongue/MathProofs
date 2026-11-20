"""Exact F3 controls for the front, label-glue, and Fourier complement formulas."""

from itertools import combinations, product
from random import Random


def dot(u, v):
    return sum(a * b for a, b in zip(u, v, strict=True)) % 3


def det(matrix):
    a = [[entry % 3 for entry in row] for row in matrix]
    answer = 1
    for i, row in enumerate(a):
        j = next((j for j in range(i, len(a)) if a[j][i]), None)
        if j is None:
            return 0
        if i != j:
            a[i], a[j] = a[j], a[i]
            answer = -answer
        pivot = a[i][i]
        answer = answer * pivot % 3
        for k in range(i + 1, len(a)):
            multiplier = a[k][i] * pivot
            a[k] = [(x - multiplier * y) % 3 for x, y in zip(a[k], a[i], strict=True)]
    return answer


def perturb(a, p, z, q):
    return [
        [(a[i][j] + sum(p[i][s] * z[s][t] * q[t][j]
                        for s in range(len(p[i])) for t in range(len(q)))) % 3
         for j in range(len(a))]
        for i in range(len(a))
    ]


def matching_indices(p, q):
    return [(rows, cols) for s in range(min(p, q) + 1)
            for rows in combinations(range(p), s) for cols in combinations(range(q), s)]


def front(p, q, response):
    result = {}
    for rows, cols in matching_indices(p, q):
        total = 0
        for indicators in product(range(2), repeat=len(rows)):
            z = [[0] * q for _ in range(p)]
            for row, col, bit in zip(rows, cols, indicators, strict=True):
                z[row][col] = bit
            total += (-1) ** (len(rows) - sum(indicators)) * response(z)
        result[rows, cols] = total % 3
    return result


def evaluate_front(response, z):
    return sum(value * det([[z[i][j] for j in cols] for i in rows])
               for (rows, cols), value in response.items()) % 3


def diagonal_front(left, right, ap, aq, bp, bq):
    out = {}
    for rows, cols in matching_indices(ap + bp, aq + bq):
        ar = tuple(i for i in rows if i < ap)
        ac = tuple(j for j in cols if j < aq)
        br = tuple(i - ap for i in rows if i >= ap)
        bc = tuple(j - aq for j in cols if j >= aq)
        out[rows, cols] = left[ar, ac] * right[br, bc] % 3 if len(ar) == len(ac) else 0
    return out


def diag(a, b, ar, ac, br, bc):
    return [row + [0] * bc for row in a] + [[0] * ac + row for row in b]


def random_matrix(random, rows, cols):
    return [[random.randrange(3) for _ in range(cols)] for _ in range(rows)]


def check_matrix_fronts(random):
    for _ in range(180):
        n, m = random.randint(1, 3), random.randint(1, 3)
        ap, aq, bp, bq = (random.randrange(3) for i in range(4))
        a, b = random_matrix(random, n, n), random_matrix(random, m, m)
        p, q = random_matrix(random, n, ap), random_matrix(random, aq, n)
        r, s = random_matrix(random, m, bp), random_matrix(random, bq, m)
        left = front(ap, aq, lambda z: det(perturb(a, p, z, q)))
        right = front(bp, bq, lambda z: det(perturb(b, r, z, s)))
        combined = diagonal_front(left, right, ap, aq, bp, bq)
        a0 = diag(a, b, n, n, m, m)
        p0 = diag(p, r, n, ap, m, bp)
        q0 = diag(q, s, aq, n, bq, m)
        for _ in range(14):
            trial = random_matrix(random, ap + bp, aq + bq)
            assert evaluate_front(combined, trial) == det(perturb(a0, p0, trial, q0))
        # Prescribe a cell crossing only the current sibling split. An arbitrary
        # embedded parent boundary port then varies on top of those crossed rows.
        z0 = random_matrix(random, ap + bp, aq + bq)
        for i in range(ap + bp):
            for j in range(aq + bq):
                if (i < ap) == (j < aq):
                    z0[i][j] = 0
        u = random_matrix(random, ap + bp, 1)
        v = random_matrix(random, 1, aq + bq)
        parent_matrix = perturb(a0, p0, z0, q0)
        for scalar in range(3):
            crossed = [[(value + scalar * u[i][0] * v[0][j]) % 3
                        for j, value in enumerate(row)] for i, row in enumerate(z0)]
            parent_p = [[dot(row, [entry[0] for entry in u])] for row in p0]
            parent_q = [[dot(v[0], [row[j] for row in q0]) for j in range(n + m)]]
            assert evaluate_front(combined, crossed) == det(perturb(parent_matrix, parent_p, [[scalar]], parent_q))


def rref(vectors, dimension):
    rows = [[entry % 3 for entry in row] for row in vectors]
    rank = 0
    pivots = []
    for j in range(dimension):
        k = next((k for k in range(rank, len(rows)) if rows[k][j]), None)
        if k is None:
            continue
        rows[k], rows[rank] = rows[rank], rows[k]
        rows[rank] = [x * rows[rank][j] % 3 for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank:
                c = rows[i][j]
                rows[i] = [(x - c * y) % 3 for x, y in zip(rows[i], rows[rank], strict=True)]
        rank += 1
        pivots.append(j)
    return tuple(map(tuple, rows[:rank])), tuple(pivots)


def kernel(vectors, dimension):
    rows, pivots = rref(vectors, dimension)
    ans = []
    for k in range(dimension):
        if k in pivots:
            continue
        vector = [int(j == k) for j in range(dimension)]
        for j, row in zip(pivots, rows, strict=True):
            vector[j] = -row[k] % 3
        ans.append(tuple(vector))
    return ans


def span(vectors, dimension):
    return rref(vectors, dimension)[0]


def meet(left, right, dimension):
    return span(kernel(kernel(left, dimension) + kernel(right, dimension), dimension), dimension)


def check_label_glue(random):
    rejected_false_assignments = 0
    kept = 0
    for _ in range(160):
        dimension = random.randint(1, 4)
        left, right, cell, exterior = [
            span(random_matrix(random, random.randrange(dimension + 1), dimension), dimension)
            for _ in range(4)
        ]
        left_boundary = meet(left, right + cell + exterior, dimension)
        right_boundary = meet(right, left + cell + exterior, dimension)
        parent_boundary = meet(left + right + cell, exterior, dimension)
        supported = left_boundary + right_boundary + cell
        positions = [len(left_boundary), len(left_boundary) + len(right_boundary)]
        relations = kernel(list(zip(*supported)), len(supported))
        assignments = list(product(range(3), repeat=dimension))

        def restrict(form, generators):
            return tuple(dot(form, row) for row in generators)

        left_options = {restrict(a, left_boundary) for a in assignments}
        right_options = {restrict(a, right_boundary) for a in assignments}
        cell_options = {restrict(a, cell) for a in assignments}
        exact = {restrict(a, supported) for a in assignments}
        actual = set()
        for l, r, c in product(left_options, right_options, cell_options):
            value = l + r + c
            assert len(l) == positions[0] and len(l + r) == positions[1]
            if all(dot(value, relation) == 0 for relation in relations):
                actual.add(value)
                kept += 1
            else:
                rejected_false_assignments += 1
        assert exact == actual
        by_boundary = {}
        for a in assignments:
            observed = restrict(a, supported)
            parent = restrict(a, parent_boundary)
            assert by_boundary.get(observed, parent) == parent
            by_boundary[observed] = parent
    assert rejected_false_assignments
    return kept, rejected_false_assignments


def trace_annihilator(rows, n):
    transposed = [tuple(row[j * n + i] for i in range(n) for j in range(n)) for row in rows]
    return span(kernel(transposed, n * n), n * n)


def sum_char(rows, n):
    total = 0
    for coefficients in product(range(3), repeat=len(rows)):
        v = [sum(c * row[j] for c, row in zip(coefficients, rows, strict=True)) % 3
             for j in range(n * n)]
        total += (0, 1, -1)[det([v[i:i + n] for i in range(0, n * n, n)])]
    return total


def check_fourier_duals():
    projective = [x for x in product(range(3), repeat=4) if any(x) and next(a for a in x if a) == 1]
    spaces = {(), span(kernel([], 4), 4)}
    spaces.update((v,) for v in projective)
    spaces.update(trace_annihilator((v,), 2) for v in projective)
    spaces.update(span((v, w), 4) for v, w in combinations(projective, 2))
    assert len(spaces) == 212
    for rows in spaces:
        # Multiply by powers of three on both sides to avoid rational arithmetic.
        exponent = len(rows) - 2
        left = sum_char(rows, 2) * 3 ** max(-exponent, 0)
        right = -sum_char(trace_annihilator(rows, 2), 2) * 3 ** max(exponent, 0)
        assert left == right

    def mask(positions):
        coordinates = [0] * 16
        for i, j in positions:
            coordinates[4 * i + j] = 1
        return tuple(coordinates)

    matrix_code = (
        mask([(0, 0), (1, 1)]), mask([(0, 1)]),
        mask([(2, 2), (3, 3)]), mask([(2, 3)]),
        mask([(0, 2)]), mask([(0, 3)]),
    )
    # For two size-two leaves, this is the example in Section 5 at its first dimension.
    k_sign = sum_char(matrix_code, 4)
    l_sign = sum_char(trace_annihilator(matrix_code, 4), 4)
    assert (k_sign, l_sign) == (324, 2916)
    return len(spaces), k_sign, l_sign


if __name__ == '__main__':
    assert __debug__
    random = Random(11409)
    check_matrix_fronts(random)
    kept, rejected = check_label_glue(random)
    controls, k_sign, l_sign = check_fourier_duals()
    print(f'180 matrix-front controls with 2520 perturbation evaluations. '
          f'160 label-glue controls with {kept} lifted and {rejected} rejected boundary assignments. '
          f'{controls} two-by-two matrix spaces and the four-by-four signs {k_sign}, {l_sign}.')
