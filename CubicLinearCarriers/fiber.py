"""One ordinary tensor for all refinements passing the polar-preimage test.

The field and cubic encodings are those of groups.py. A tensor exposes its
ordinary unpartitioned shape and exact coefficient lookup at zero-based indices.
The final rank markers have large absolute constants. Random access avoids
allocating their zero entries. The dense array can be materialized from entry.
"""
from dataclasses import dataclass
from itertools import combinations_with_replacement
from groups import Field


def refinement_mark(k, n, cubic):
    """Return the canonical covector, or None if the sufficient test fails."""
    terms = sorted(combinations_with_replacement(range(n), 3),
                   key=lambda t: (t[0] == t[2], t))
    index = {t: i for i, t in enumerate(terms)}
    mixed = len(terms)-n
    pivots = {}

    def eliminate(v):
        for i in sorted(pivots):
            if v[i]:
                u = k.mul(2, v[i])
                v = [k.add(a, k.mul(u, b)) for a, b in zip(v, pivots[i])]
        return v

    for a in range(n):
        for b in range(n):
            col = [0]*len(terms)
            for term, coefficient in cubic.items():
                for j, x in enumerate(term):
                    if x == a:
                        t = list(term)
                        t[j] = b
                        i = index[tuple(sorted(t))]
                        col[i] = k.add(col[i], coefficient)
            col = eliminate(col)
            lead = next((i for i in range(mixed) if col[i]), None)
            if lead is None:
                if any(col[mixed:]):
                    return None
            else:
                inv = k.power(col[lead], k.q-2)
                pivots[lead] = [k.mul(inv, x) for x in col]
    residual = eliminate([cubic.get(t, 0) for t in terms])
    if any(residual[:mixed]):
        return None
    return tuple(k.power(v, k.q//3) for v in residual[mixed:])


@dataclass
class Tensor:
    parts: tuple
    coefficient: object

    @property
    def shape(self):
        return tuple(sum(axis) for axis in self.parts)

    def entry(self, i, j, k):
        if any(not 0 <= x < d for x, d in zip((i, j, k), self.shape)):
            raise IndexError("Tensor coordinate outside its shape.")
        return self.coefficient(i, j, k)


def decolor(tensor, axis):
    """Duplicate-tag field construction, with private identity blocks stored by intervals."""
    row, col, layer = axis, (axis+1) % 3, (axis+2) % 3
    p, m, layers = (tensor.shape[i] for i in (row, col, layer))
    tags = []
    old_start = 0
    new_row, new_col = p, m
    for width in tensor.parts[row]:
        for _ in range(2):
            rank = (p+m+1)*(1 << len(tags))
            tags.append((old_start, width, new_row, new_col, rank))
            new_row += m+rank
            new_col += width+rank
        old_start += width

    def coefficient(*coords):
        x, y, z = (coords[i] for i in (row, col, layer))
        if z < layers:
            return tensor.coefficient(*coords) if x < p and y < m else 0
        start, width, yrow, xcol, rank = tags[z-layers]
        return int((0 <= y < m and x == yrow+y)
                   or (0 <= x-start < width and y == xcol+x-start)
                   or (0 <= x-(yrow+m) < rank and x-(yrow+m) == y-(xcol+width)))

    parts = [list(blocks) for blocks in tensor.parts]
    parts[row] = [new_row]
    parts[col][-1] += new_col-m
    parts[layer][-1] += len(tags)
    return Tensor(tuple(tuple(blocks) for blocks in parts), coefficient)


def fiber_tensor(field, n, cubic):
    """Return the single ordinary tensor, or None outside this theorem's rank test."""
    if n <= 0:
        raise ValueError("A positive number of variables is required.")
    mark = refinement_mark(field, n, cubic)
    if mark is None:
        return None
    scalar = 2*n

    def data(i, j, z):
        if i < n and j < n and z < n:
            t = tuple(sorted((i, j, z)))
            factor = (0, 2, 1)[len(set(t))-1]
            return field.mul(factor, cubic.get(t, 0))
        if z == n:
            if i == j == scalar:
                return 1
            if i < n and j == scalar:
                return mark[i]
            return int((i < n and j == n+i) or (j < n and i == n+j))
        return int((i == scalar and j == n+z) or (j == scalar and i == n+z))

    tensor = Tensor(((n,n,1), (n,n,1), (n,1)), data)
    for axis in range(3):
        tensor = decolor(tensor, axis)
    return tensor
