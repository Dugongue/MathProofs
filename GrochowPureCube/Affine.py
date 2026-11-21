"""Exact finite checks for the marked-cubic lift formula and affine example."""
from itertools import product
from collections import Counter


def gl(size):
    """List invertible matrices over F3, by rows."""
    for rows in product(list(product(range(3), repeat=size)), repeat=size):
        if size == 2:
            determinant = rows[0][0] * rows[1][1] - rows[0][1] * rows[1][0]
        else:
            a, b, c = rows
            determinant = (
                a[0] * (b[1] * c[2] - b[2] * c[1])
                - a[1] * (b[0] * c[2] - b[2] * c[0])
                + a[2] * (b[0] * c[1] - b[1] * c[0])
            )
        if determinant % 3:
            yield rows


def substitution_basis(matrix):
    """Formal coefficients of (Mx)_0²(Mx)_1 and of each pure cube."""
    n = len(matrix)
    mixed = Counter()
    for i, j, h in product(range(n), repeat=3):
        mixed[tuple(sorted((i, j, h)))] += matrix[0][i] * matrix[0][j] * matrix[1][h]
    pure = {index: mixed.pop((index,) * 3, 0) for index in range(n)}
    return {key: value % 3 for key, value in mixed.items() if value % 3}, pure


def act(row, matrix):
    return tuple(sum(value * matrix[i][j] for i, value in enumerate(row)) % 3
                 for j in range(len(matrix)))


def combine(mixed_pure, weights, matrix):
    linear = act(weights, matrix)
    return tuple((mixed_pure[i] + coefficient) % 3
                 for i, coefficient in enumerate(linear))


def radical_data(weights, marks):
    """One radical coordinate. Elements of J and its projection."""
    last = tuple(mark[2] for mark in marks) + (weights[2],)
    image = {tuple(a * value % 3 for value in last) for a in range(3)}
    return image, {point[:-1] for point in image}


def quotient_count(source, target, matrices):
    fa, fm = source
    ga, gm = target
    j_f, i_f = radical_data(fa, fm)
    j_g, _ = radical_data(ga, gm)
    if j_f != j_g:
        return 0
    absorbed = (0,) * len(fm) + (1,) in j_f
    graph = dict((point[:-1], point[-1]) for point in j_f)
    count = 0
    for matrix, mixed_pure in matrices:
        differences = [tuple((x - y) % 3 for x, y in zip(row[:2], act(tgt[:2], matrix)))
                       for row, tgt in zip(fm, gm)]
        mark_diffs = list(zip(*differences)) if differences else [(), ()]
        if any(diff not in i_f for diff in mark_diffs):
            continue
        rewritten = combine(mixed_pure, ga[:2], matrix)
        discrepancy = tuple((fa[i] - rewritten[i]) % 3 for i in range(2))
        if absorbed or discrepancy == tuple(graph[diff] for diff in mark_diffs):
            count += 1
    # Formula (1) with c=2 and r=1.
    return count if len(j_f) == 3 else 18 * count


def check_marked():
    # These examples share polarization x²y. The last variable is its radical.
    zero = (0, 0, 0)
    x, y, z = (1, 0, 0), (0, 1, 0), (0, 0, 1)
    xz, yz = (1, 0, 1), (0, 1, 1)
    one_mark = [(pure, (mark,)) for pure in (zero, y, z, xz)
                for mark in (zero, x, z, yz)]
    two_marks = [(pure, marks) for pure in (zero, y, z, xz)
                 for marks in ((x, y), (x, z), (xz, yz), (z, z))]
    families = [one_mark, two_marks]
    quotient = [(matrix, pure) for matrix in gl(2)
                for mixed, pure in [substitution_basis(matrix)] if mixed == {(0, 0, 1): 1}]
    checks = [(matrix, pure) for matrix in gl(3)
              for mixed, pure in [substitution_basis(matrix)] if mixed == {(0, 0, 1): 1}]
    regimes = set()
    for cases in families:
        for target in cases:
            weights, marks = target
            orbit = Counter()
            for matrix, mixed_pure in checks:
                coefficients = combine(mixed_pure, weights, matrix)
                transported_marks = tuple(act(row, matrix) for row in marks)
                orbit[coefficients, transported_marks] += 1
            for source in cases:
                predicted = quotient_count(source, target, quotient)
                exact = orbit[source]
                assert predicted == exact, (source, target, predicted, exact)
                image, _ = radical_data(source[0], source[1])
                if exact:
                    regimes.add((len(image), (0,) * len(source[1]) + (1,) in image))
    assert regimes == {(1, False), (3, False), (3, True)}
    print(f"{sum(len(cases) ** 2 for cases in families)} marked pairs passed; "
          f"{len(checks)} relevant ternary substitutions and all three radical regimes.")


def check_trace():
    # F9 = F3[i] with i² = -1.
    def mul(x, y):
        return ((x[0] * y[0] - x[1] * y[1]) % 3, (x[0] * y[1] + x[1] * y[0]) % 3)

    elements = list(product(range(3), repeat=2))
    cubes = {x: mul(x, mul(x, x)) for x in elements}
    traces = {x: (x[0] + cubes[x][0]) % 3 for x in elements}
    orbit = Counter(tuple((a - b) % 3 for a, b in zip(cubes[x], x)) for x in elements)
    for a, b in product(elements, repeat=2):
        difference = tuple((t - s) % 3 for s, t in zip(a, b))
        assert orbit[difference] == (3 if traces[a] == traces[b] else 0)
    print("All 81 ordered translations-in-constant examples over F9 passed.")


if __name__ == "__main__":
    check_marked()
    check_trace()
