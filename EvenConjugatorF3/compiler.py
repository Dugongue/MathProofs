"""Compile full symmetric-square relation spaces to one ordinary TI over F3.

A dense table has one row per output coordinate and columns beta(e_i,e_j)
in lexicographic order on 0 <= i <= j < n. Its map Sym^2 X -> Z must be onto.
The algorithm applies for even n and R = Sym^2 B with odd dim B.
Run directly with Python 3 for reproducible changes-of-basis controls.
"""

from itertools import combinations_with_replacement
from random import Random


def rref(matrix):
    a = [[v % 3 for v in row] for row in matrix]
    pivots = []
    for j in range(len(a[0])):
        k = len(pivots)
        p = next((i for i in range(k, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[k], a[p] = a[p], a[k]
        t = a[k][j]
        a[k] = [v * t % 3 for v in a[k]]
        for i in range(len(a)):
            if i != k and a[i][j]:
                t = a[i][j]
                a[i] = [(v - t * w) % 3 for v, w in zip(a[i], a[k])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return a, pivots


def det(matrix):
    a = [[v % 3 for v in row] for row in matrix]
    result = 1
    for j in range(len(a)):
        p = next((i for i in range(j, len(a)) if a[i][j]), None)
        if p is None:
            return 0
        if p != j:
            a[p], a[j] = a[j], a[p]
            result = -result
        t = a[j][j]
        result = result * t % 3
        for i in range(j + 1, len(a)):
            k = a[i][j] * t % 3
            if k:
                a[i] = [(v - k * w) % 3 for v, w in zip(a[i], a[j])]
    return result


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def multiply(a, b):
    cols = list(zip(*b))
    return [[sum(x*y for x, y in zip(row, col)) % 3 for col in cols] for row in a]


def symmetric_square(g, pairs):
    return [[(g[i][a]*g[j][b] + (i != j)*g[j][a]*g[i][b]) % 3
             for a, b in pairs] for i, j in pairs]


def endpoint(n, table):
    pairs = list(combinations_with_replacement(range(n), 2))
    if not n or n % 2 or not table or any(len(row) != len(pairs) for row in table):
        raise ValueError("Expected even positive input dimension and a dense quotient table")
    red, pivots = rref(table)
    if len(pivots) != len(table):
        raise ValueError("The quotient table must be onto")
    free = sorted(set(range(len(pairs))) - set(pivots))

    # Every kernel basis vector is a quadratic polynomial. Its first partial
    # derivatives generate its support, since 2 is invertible over F3.
    derivatives = []
    for f in free:
        relation = [0] * len(pairs)
        relation[f] = 1
        for i, p in enumerate(pivots):
            relation[p] = -red[i][f] % 3
        gradient = [[0]*n for _ in range(n)]
        for (i, j), v in zip(pairs, relation):
            gradient[i][j] = (gradient[i][j] + v) % 3
            gradient[j][i] = (gradient[j][i] + v) % 3
        derivatives.extend(gradient)

    candidates = derivatives + identity(n)
    _, basis_indices = rref(list(zip(*candidates)))
    s = sum(i < len(derivatives) for i in basis_indices)
    if s % 2 != 1 or len(free) != s*(s+1)//2:
        raise ValueError("Relations must fill the symmetric square of an odd-dimensional support")
    basis = list(zip(*(candidates[i] for i in basis_indices)))
    images = multiply(table, symmetric_square(basis, pairs))
    quotient_basis = [[v for v, (_, j) in zip(row, pairs) if j >= s] for row in images]
    orientation = det(basis) * det(quotient_basis) % 3
    if orientation == 0:
        raise ArithmeticError("Adapted quotient basis is singular")
    return s, orientation


UNIT_TENSOR = (((1,),),)
ZERO_TENSOR = (((0,),),)


def compile_even(n_source, source, n_target, target):
    """Return two explicit 1 x 1 x 1 tensors, isomorphic iff an even map exists."""
    s, a = endpoint(n_source, source)
    t, b = endpoint(n_target, target)
    yes = (n_source, len(source), s, a) == (n_target, len(target), t, b)
    return UNIT_TENSOR, UNIT_TENSOR if yes else ZERO_TENSOR


def basis_change(n, determinant, rng):
    g = identity(n)
    for _ in range(4*n):
        i, j = rng.sample(range(n), 2)
        t = rng.choice((1, 2))
        g[i] = [(v+t*w) % 3 for v, w in zip(g[i], g[j])]
    if determinant == 2:
        g[0] = [(-v) % 3 for v in g[0]]
    return g


def inverse(g):
    n = len(g)
    augmented = [row + unit for row, unit in zip(g, identity(n))]
    red, pivots = rref(augmented)
    assert pivots == list(range(n))
    return [row[n:] for row in red]


def controls():
    rng = Random(20261121)
    n, s = 6, 3
    pairs = list(combinations_with_replacement(range(n), 2))
    original = [[int(p == q) for q in pairs] for p in pairs if p[1] >= s]
    answers = {True: 0, False: 0}
    moved = 0
    for dg in (1, 2):
        for dh in (1, 2):
            for _ in range(6):
                g, h = basis_change(n, dg, rng), basis_change(len(original), dh, rng)
                assert det(g) == dg and det(h) == dh
                moved += any(g[i][j] for i in range(s, n) for j in range(s))
                target = multiply(multiply(h, original), symmetric_square(inverse(g), pairs))
                ordinary = compile_even(n, original, n, target)
                even = ordinary[0] == ordinary[1]
                assert even == (dg*dh % 3 == 1)
                answers[even] += 1
    assert moved == sum(answers.values())
    print(f"Split (6,15) arbitrary-basis controls passed: {sum(answers.values())} "
          f"({answers[True]} YES, {answers[False]} NO); support moved in {moved}.")


if __name__ == "__main__":
    controls()
