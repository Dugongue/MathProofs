"""Check the adjoint-envelope certificate for sl(3) in characteristic two."""
from collections import deque


def unit(row, col):
    return 1 << (3 * row + col)


def multiply_small(a, b):
    result = 0
    for i in range(3):
        for j in range(3):
            if a & unit(i, j):
                for k in range(3):
                    if b & unit(j, k):
                        result ^= unit(i, k)
    return result


def span_coordinates(basis):
    coordinates = {0: 0}
    for i, vector in enumerate(basis):
        new = {v ^ vector: mask | (1 << i) for v, mask in coordinates.items()}
        assert coordinates.keys().isdisjoint(new)
        coordinates.update(new)
    return coordinates


def compose(a, b, d):
    """Matrices store columns as consecutive d-bit chunks."""
    result = 0
    mask = (1 << d) - 1
    for j in range(d):
        column = (b >> (j * d)) & mask
        for i in range(d):
            if column & (1 << i):
                result ^= ((a >> (i * d)) & mask) << (j * d)
    return result


def envelope_dimension(generators, d):
    identity = sum(1 << (i * (d + 1)) for i in range(d))
    queue = deque([(identity, 0)])
    pivots = {}
    last_length = 0
    while queue:
        word, length = queue.popleft()
        reduced = word
        while reduced:
            pivot = reduced.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = reduced
                last_length = length
                queue.extend((compose(g, word, d), length + 1) for g in generators)
                break
            reduced ^= pivots[pivot]
    return len(pivots), last_length


def main():
    basis = [unit(i, j) for i in range(3) for j in range(3) if i != j]
    basis += [unit(0, 0) ^ unit(1, 1), unit(1, 1) ^ unit(2, 2)]
    coords = span_coordinates(basis)
    d = len(basis)
    generators = []
    for x in basis:
        columns = [coords[multiply_small(x, y) ^ multiply_small(y, x)] for y in basis]
        generators.append(sum(v << (j * d) for j, v in enumerate(columns)))
    dim, length = envelope_dimension(generators, d)
    assert dim == d * d == 64
    print(f"Adjoint words of length at most {length} span all {dim} matrix coordinates over F2.")


if __name__ == "__main__":
    main()
