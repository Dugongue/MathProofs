"""Exact finite controls for the cubic-system closure examples over F_3."""

from itertools import combinations_with_replacement, product


Q = 3


def invertible(n):
    vectors = tuple(product(range(Q), repeat=n))

    def extend(rows, span):
        if len(rows) == n:
            yield rows
            return
        for row in vectors:
            if row in span:
                continue
            next_span = {
                tuple((a + t * b) % Q for a, b in zip(vector, row))
                for vector in span
                for t in range(Q)
            }
            yield from extend(rows + (row,), next_span)

    yield from extend((), {(0,) * n})


def substitute(monomial, matrix):
    """Coefficients of a monomial evaluated on row linear forms."""
    n = len(matrix)
    out = {}
    i, j, k = monomial
    for a, b, c in product(range(n), repeat=3):
        key = tuple(sorted((a, b, c)))
        out[key] = (out.get(key, 0) + matrix[i][a] * matrix[j][b] * matrix[k][c]) % Q
    return {key: value for key, value in out.items() if value}


def discriminate(coefficients):
    a, b, c, d = coefficients
    return (b * b * c * c - b**3 * d - a * c**3) % Q


def ordered_control():
    f = (0, 0, 1)
    monomials = tuple(combinations_with_replacement(range(2), 3))
    discriminants = {
        discriminate(tuple(substitute(f, matrix).get(key, 0) for key in monomials))
        for matrix in invertible(2)
    }
    assert discriminants == {0} and discriminate((0, 1, 0, 1)) == 2

    # The mixed monomials and the second cubic are fixed by retaining
    # substitutions that fix x^2 y exactly. Cubing the third row adds z^3.
    retained = set()
    for matrix in invertible(3):
        if substitute(f, matrix) == {f: 1}:
            retained.add(matrix[2])
    expected = {
        (a, b, c) for a, b in product(range(Q), repeat=2) for c in (1, 2)
    }
    assert retained == expected
    print("ordered product: 18 orbit lifts, 9 rank-drop lifts in 27-point affine slice")


def lines(n):
    for vector in product(range(Q), repeat=n):
        if next((v for v in vector if v), None) == 1:
            yield vector


def variable_control():
    output_lines = tuple(lines(2))
    input_lines = tuple(lines(3))
    first = (1, 0)
    # Target J=(x^3,0). On these flags the quotient pair is zero or a
    # nonzero pure cube, both witnessed by the substitutions in the proof.
    flags = {
        (plane, line)
        for plane, line in product(input_lines, output_lines)
        if plane[0] == 0 or line == first
    }
    vertical = {(plane, first) for plane in input_lines}
    horizontal = {
        (plane, line) for plane, line in product(input_lines, output_lines)
        if plane[0] == 0
    }
    assert flags == vertical | horizontal
    assert (len(flags), len(vertical), len(horizontal), len(vertical & horizontal)) == (
        25, 13, 16, 4
    )
    print("reducible left-right fiber: 25 flags, component counts 13 and 16, intersection 4")


def thickening_control():
    # The triple-line chart at a fixed reduced point has a free coordinate
    # with zero residue and the transverse equation b^3=0.
    def cube(value):
        return (value[0], 0, 0, value[1])

    nilpotent_coordinates = [(0, *tail) for tail in product(range(Q), repeat=3)]
    transverse = [b for b in nilpotent_coordinates if cube(b) == (0, 0, 0, 0)]
    assert len(transverse) == 9
    assert len(nilpotent_coordinates) * len(transverse) == 243
    print("one triple-line chart over F_3[e]/(e^4): 243 lifts, 27 reduced lifts")


if __name__ == "__main__":
    ordered_control()
    variable_control()
    thickening_control()

