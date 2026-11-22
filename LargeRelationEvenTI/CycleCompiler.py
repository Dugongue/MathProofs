"""Compile the ternary cycle-relation branch from two dense bimap tables.

Call compile_even(n, source, m, target). Each row is one output coordinate and
columns index unordered input pairs in lexicographic order. Both input sizes
must be positive and even. The supported relation graphs are disjoint cycles
of pairwise distinct lengths 1 mod 4, each at least 5. Unsupported endpoints
raise ValueError. An ordinary tensor is a tuple indexed by its three modes.
"""

from itertools import combinations_with_replacement
from random import Random


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def pack(row):
    positive = negative = 0
    for j, entry in enumerate(row):
        value = entry % 3
        if value == 1:
            positive |= 1 << j
        elif value == 2:
            negative |= 1 << j
    return positive, negative


def unpack(row, width):
    p, n = row
    return [((p >> j) & 1) + 2*((n >> j) & 1) for j in range(width)]


def add_packed(x, y):
    xp, xn = x
    yp, yn = y
    xzero = ~(xp | xn)
    yzero = ~(yp | yn)
    return ((xp & yzero) | (yp & xzero) | (xn & yn),
            (xn & yzero) | (yn & xzero) | (xp & yp))


def reduce(matrix, width, pivot_limit=None):
    rows = [pack(row) for row in matrix]
    pivots = []
    determinant = 1
    for j in range(width if pivot_limit is None else pivot_limit):
        i = len(pivots)
        bit = 1 << j
        k = next((k for k in range(i, len(rows)) if (rows[k][0] | rows[k][1]) & bit), None)
        if k is None:
            continue
        if k != i:
            rows[i], rows[k] = rows[k], rows[i]
            determinant = -determinant
        if rows[i][1] & bit:
            rows[i] = rows[i][::-1]
            determinant = -determinant
        positive = rows[i]
        negative = positive[::-1]
        for k, row in enumerate(rows):
            if k == i:
                continue
            if row[0] & bit:
                rows[k] = add_packed(row, negative)
            elif row[1] & bit:
                rows[k] = add_packed(row, positive)
        pivots.append(j)
        if len(pivots) == len(rows):
            break
    return [unpack(row, width) for row in rows[:len(pivots)]], pivots, determinant % 3


def kernel_basis(reduced, pivots, width):
    basis = []
    for j in sorted(set(range(width)).difference(pivots)):
        v = [0] * width
        v[j] = 1
        for i, p in enumerate(pivots):
            v[p] = -reduced[i][j] % 3
        basis.append(v)
    return basis


def apply_matrix(matrix, v):
    return [sum(x*y for x, y in zip(row, v)) % 3 for row in matrix]


def product_coordinates(u, v, pairs):
    return [(u[i]*v[j] + (i != j)*u[j]*v[i]) % 3 for i, j in pairs]


def endpoint(n, table):
    pairs = list(combinations_with_replacement(range(n), 2))
    width = len(pairs)
    size = len(table)
    if n < 1 or n % 2 or size < 1 or any(len(row) != width for row in table):
        raise ValueError("Expected even positive input dimension and a nonempty dense quotient table")
    indices = {pair: i for i, pair in enumerate(pairs)}
    pair_index = [[indices[min(i, j), max(i, j)] for j in range(n)] for i in range(n)]
    augmented = [list(row)+u for row, u in zip(table, identity(size))]
    reduced, pivots, _ = reduce(augmented, width+size, width)
    if len(pivots) != size:
        raise ValueError("Output must be spanned")
    relations = kernel_basis(reduced, pivots, width)
    if len(relations) != n:
        raise ValueError("A disjoint union of cycles has one edge per vertex")

    # For each r, the E_ki derivative is x_k times the i-th partial of r.
    # Read its image in the given quotient directly, one output row at a time.
    equations = []
    for r in relations:
        gradient = [[0]*n for _ in range(n)]
        for value, (i, j) in zip(r, pairs):
            gradient[i][j] += value
            gradient[j][i] += value
        terms = [[(j, value % 3) for j, value in enumerate(row) if value % 3]
                 for row in gradient]
        for row in table:
            equations.append([sum(t*row[pair_index[k][j]] for j, t in terms[i]) % 3
                              for k in range(n) for i in range(n)])
    reduced_d, pivots_d, _ = reduce(equations, n*n)
    derivations = kernel_basis(reduced_d, pivots_d, n*n)
    if len(derivations) != n:
        raise ValueError("Expected a split diagonal derivation algebra of dimension n")

    spaces = [identity(n)]
    for flat in derivations:
        matrix = [flat[i*n:(i+1)*n] for i in range(n)]
        new_spaces = []
        for basis in spaces:
            if len(basis) == 1:
                new_spaces.append(basis)
                continue
            image = [apply_matrix(matrix, v) for v in basis]
            for scalar in range(3):
                equations = [[(w[i]-scalar*v[i]) % 3 for w, v in zip(image, basis)]
                             for i in range(n)]
                echelon, leading, _ = reduce(equations, len(basis))
                kernel = kernel_basis(echelon, leading, len(basis))
                if kernel:
                    new_spaces.append([apply_matrix(zip(*basis), v) for v in kernel])
        if sum(map(len, new_spaces)) != n:
            raise ValueError("Derivations do not split into eigenspaces")
        spaces = new_spaces
        if len(spaces) == n:
            break
    if len(spaces) != n:
        raise ValueError("Derivations do not recover individual vertex lines")
    frame = [space[0] for space in spaces]
    adjacency = [set() for _ in range(n)]
    coordinates = {}
    for i, j in pairs:
        v = product_coordinates(frame[i], frame[j], pairs)
        if any(apply_matrix(table, v)):
            continue
        if i == j:
            raise ValueError("The recovered graph has a loop")
        adjacency[i].add(j)
        adjacency[j].add(i)
        coordinates[i, j] = v
    if len(coordinates) != len(relations) or any(len(row) != 2 for row in adjacency):
        raise ValueError("The recovered relations are not a disjoint union of cycles")

    # A traversal lists the cycle edges. Permitted changes of traversal have
    # even sign in this branch. Distinct lengths order the cycles intrinsically.
    remaining = set(range(n))
    cycles = {}
    while remaining:
        start = min(remaining)
        previous, vertex = start, min(adjacency[start])
        edges = [(min(start, vertex), max(start, vertex))]
        while vertex != start:
            neighbor, = adjacency[vertex] - {previous}
            edges.append((min(vertex, neighbor), max(vertex, neighbor)))
            previous, vertex = vertex, neighbor
        remaining.difference_update(v for edge in edges for v in edge)
        length = len(edges)
        if length < 5 or length % 4 != 1 or length in cycles:
            raise ValueError("Cycle lengths must be distinct, at least five and 1 modulo 4")
        cycles[length] = edges
    columns = [coordinates[edge] for length in sorted(cycles) for edge in cycles[length]]
    for i in range(size):
        lift = [0]*width
        for j, p in enumerate(pivots):
            lift[p] = reduced[j][width+i]
        columns.append(lift)
    _, basis_pivots, determinant = reduce(columns, width)
    if len(basis_pivots) != width:
        raise ArithmeticError("The relation basis and quotient lifts must be complementary")
    return tuple(sorted(cycles)), determinant


UNIT = (((1,),),)
ZERO = (((0,),),)


def compile_even(n, source, m, target):
    """Return one ordinary tensor pair for the two supported quotient tables."""
    return UNIT, UNIT if endpoint(n, source) == endpoint(m, target) else ZERO


def example(lengths):
    n = sum(lengths)
    pairs = list(combinations_with_replacement(range(n), 2))
    edges = set()
    start = 0
    for length in lengths:
        for i in range(length):
            a = start+i
            b = start+(i+1) % length
            edges.add((min(a, b), max(a, b)))
        start += length
    return [[int(p == q) for p in pairs] for q in pairs if q not in edges]


def scramble(n, table, rng, odd_input=False, odd_output=False):
    result = [list(row) for row in table]
    pairs = list(combinations_with_replacement(range(n), 2))
    index = {pair: k for k, pair in enumerate(pairs)}

    def pos(i, j):
        return index[min(i, j), max(i, j)]

    for _ in range(5*n):
        u, v = rng.sample(range(n), 2)
        t = rng.choice((1, 2))
        for row in result:
            row[pos(u, u)] = (row[pos(u, u)] + 2*t*row[pos(u, v)] + t*t*row[pos(v, v)]) % 3
            for j in range(n):
                if j != u:
                    row[pos(u, j)] = (row[pos(u, j)] + t*row[pos(v, j)]) % 3
    for _ in range(4*len(result)):
        u, v = rng.sample(range(len(result)), 2)
        result[u] = [(a+b) % 3 for a, b in zip(result[u], result[v])]
    if odd_input:
        for row in result:
            for j in range(1, n):
                row[pos(0, j)] = -row[pos(0, j)] % 3
    if odd_output:
        result[0] = [(-a) % 3 for a in result[0]]
    return result


def controls():
    rng = Random(261121)
    n = 14
    raw = example((5, 9))
    source = scramble(n, raw, rng, odd_input=True, odd_output=True)
    counts = [0, 0]
    for input_flip in (False, True):
        for output_flip in (False, True):
            target = scramble(n, raw, rng, input_flip, output_flip)
            pair = compile_even(n, source, n, target)
            assert (pair == (UNIT, UNIT)) == (input_flip == output_flip)
            counts[int(input_flip == output_flip)] += 1
    print(f"Four dense (14,91) comparisons passed: {counts[1]} even and {counts[0]} odd-only.")


if __name__ == "__main__":
    controls()
