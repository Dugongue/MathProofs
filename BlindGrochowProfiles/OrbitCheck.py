"""Direct finite checks for the permutation tuple benchmark. Uses only the standard library."""
from itertools import product
from math import prod
import json


def add_scaled(x, y, a, p):
    return tuple((i + a * j) % p for i, j in zip(x, y))


def subspaces(points, p):
    zero = frozenset([points[0]])
    seen = {zero}
    pending = [zero]
    while pending:
        h = pending.pop()
        for x in points:
            if x in h:
                continue
            span = frozenset(add_scaled(w, x, a, p) for w in h for a in range(p))
            if span not in seen:
                pending.append(span)
                seen.add(span)
    return seen


def first_identity(points, spaces, p):
    # Columns of the direct sum of quotient actions on their identity basis vectors.
    # A group algebra element vanishes on a quotient regular module iff this column is zero.
    coordinates = []
    row_count = 0
    for line in (h for h in spaces if len(h) == p):
        indices = {}
        for x in points:
            if x not in indices:
                for y in line:
                    indices[add_scaled(x, y, 1, p)] = row_count
                row_count += 1
        coordinates.append(indices)

    pivots = {}
    for x in sorted(points, key=sum):
        # g^x for x in [0,p-1]^r of bounded degree are independent on the regular side.
        column = [0] * row_count
        for indices in coordinates:
            column[indices[x]] = 1
        for i in range(row_count):
            value = column[i]
            if not value:
                continue
            if i not in pivots:
                inv = pow(value, -1, p)
                pivots[i] = [(v * inv) % p for v in column]
                break
            column = [(a - value * b) % p for a, b in zip(column, pivots[i])]
        else:
            return sum(x)
    raise AssertionError("missing identity")


def trial(p, r):
    points = list(product(range(p), repeat=r))
    spaces = subspaces(points, p)
    counts = {}
    for h in spaces:
        j = next(j for j in range(r+1) if len(h) * p**j == len(points))
        counts[h] = (-1)**j * p**(1 + j*(j-1)//2 - j)
    dimensions = [sum(abs(c) * len(points)//len(h) for h, c in counts.items()
                      if c*sign > 0) for sign in (1, -1)]
    assert dimensions == [p*prod(1+p**i for i in range(1, r))]*2
    for u in spaces:
        mark = sum(c * len(points)//len(h) for h, c in counts.items() if u <= h)
        assert mark == (p if len(u) == len(points) else 0)
    first = first_identity(points, spaces, p)
    assert first == (r-1)*(p-1)+1
    free_orbits = counts[frozenset([points[0]])]
    return dict(p=p, r=r, dimension=dimensions[0], proper_subgroups=len(spaces)-1,
                regular_orbit_difference=free_orbits, first_identity=first)


if __name__ == "__main__":
    cases = [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (5, 2), (7, 2)]
    print(json.dumps([trial(p, r) for p, r in cases], indent=2))
