"""Exact three-vertex control. Run with standard Python 3; no dependencies."""
from fractions import Fraction as F
from itertools import combinations, product
from collections import Counter
from functools import cache
from three_vertex import three_vertex_margin

# At each of the three vertices the two trace-zero weights are x and -x.
# Enumerate all nonempty supports of the eight separate matrix-unit arrows.
ARCS = [(2*v+i, 2*v+2+j) for v in range(2) for i in range(2) for j in range(2)]


def dot(a, b):
    return sum(x*y for x, y in zip(a, b))


def arrow_row(edge):
    source, target = edge
    row = [0, 0, 0]
    row[source//2] -= (-1)**(source % 2)
    row[target//2] += (-1)**(target % 2)
    return tuple(row)


def solve(matrix, rhs):
    n = len(rhs)
    aug = [list(map(F, row)) + [F(b)] for row, b in zip(matrix, rhs)]
    for i in range(n):
        pivot = next((j for j in range(i, n) if aug[j][i]), None)
        if pivot is None:
            return None
        aug[i], aug[pivot] = aug[pivot], aug[i]
        aug[i] = [v/aug[i][i] for v in aug[i]]
        for j in range(n):
            if j != i:
                a = aug[j][i]
                aug[j] = [v-a*w for v, w in zip(aug[j], aug[i])]
    return [row[-1] for row in aug]


@cache
def nearest(active):
    gram = [[dot(a, b) for b in active] for a in active]
    z = solve(gram, [1]*len(active))
    if z is not None:
        return tuple(dot(z, col) for col in zip(*active))


def primal(edges):
    rows = tuple(map(arrow_row, edges))
    norms = []
    for k in range(1, 4):
        for active in combinations(rows, k):
            x = nearest(active)
            if x is not None and all(dot(r, x) >= 1 for r in rows):
                norms.append(2*dot(x, x))
    return 1/min(norms) if norms else F(0)


# Prices obey 2 sum(lambda)=0 and 2(lambda_0-lambda_2)=1.
BASE = (F(1, 4), F(0), F(-1, 4))
DIRECTION = (1, -2, 1)
DIMS = sorted(set(tuple(bits[2*i:2*i+2].count(1) for i in range(3))
                  for bits in product(range(2), repeat=6)))
SLOPES = {e: (dot(BASE, e)/sum(e), F(dot(DIRECTION, e), sum(e)))
          for e in DIMS if sum(e)}
WALLS = sorted({(b-a)/(da-db) for (a, da), (b, db) in combinations(SLOPES.values(), 2)
                if da != db})


def ideals(edges):
    dims = set()
    for bits in product(range(2), repeat=6):
        if all(bits[i] <= bits[j] for i, j in edges):
            dims.add(tuple(sum(bits[2*i:2*i+2]) for i in range(3)))
    return dims


def quadratic(dims, t):
    # The upper concave hull of (total dimension, price) is the HN polygon.
    high = {}
    for e in dims:
        s = sum(e)
        price = dot(BASE, e) + t*dot(DIRECTION, e)
        if s not in high or high[s][0] < price:
            high[s] = (price, e)
    hull = []
    for s, (y, e) in sorted(high.items()):
        while len(hull) >= 2:
            x0, y0, _ = hull[-2]
            x1, y1, _ = hull[-1]
            if (y1-y0)*(s-x1) > (y-y1)*(x1-x0):
                break
            hull.pop()
        hull.append((s, y, e))
    a = b = c = F(0)
    for left, right in zip(hull, hull[1:]):
        e = tuple(y-x for x, y in zip(left[2], right[2]))
        ds = right[0] - left[0]
        u, v = dot(BASE, e), dot(DIRECTION, e)
        a += F(v*v, ds)
        b += 2*u*v/ds
        c += u*u/ds
    return a, b, c


def dual(edges):
    dims = ideals(edges)
    calls = 0

    def query(t):
        nonlocal calls
        calls += 1
        return quadratic(dims, t)

    lo, hi = -1, len(WALLS)
    eta = None
    while hi-lo > 1:
        mid = (lo+hi)//2
        t = WALLS[mid]
        a, b, c = query(t)
        derivative = 2*a*t + b
        if derivative == 0:
            eta = (a*t+b)*t+c
            break
        if derivative < 0:
            lo = mid
        else:
            hi = mid
    if eta is None:
        if lo < 0:
            sample = WALLS[hi]-1
        elif hi == len(WALLS):
            sample = WALLS[lo]+1
        else:
            sample = (WALLS[lo]+WALLS[hi])/2
        a, b, c = query(sample)
        t = -b/(2*a) if a else sample
        assert a or b == 0
        assert lo < 0 or WALLS[lo] <= t
        assert hi == len(WALLS) or t <= WALLS[hi]
        eta = (a*t+b)*t+c
    assert 0 <= eta < F(1, 4)  # C=4 and at least one arrow.
    return (eta/(1-4*eta)), calls


def coordinate_principal(edges):
    """Return an exhaustive principal-filtration routine for this six-coordinate test."""
    closed = []
    for mask in range(64):
        if all(not (mask >> i & 1) or mask >> j & 1 for i, j in edges):
            e = tuple(((mask >> (2*i)) & 3).bit_count() for i in range(3))
            closed.append((mask, e))

    def principal(price):
        current = 0
        result = []
        while current != 63:
            best = None
            next_step = None
            for mask, _ in closed:
                if mask == current or current & ~mask:
                    continue
                added = mask ^ current
                e = tuple(((added >> (2*i)) & 3).bit_count() for i in range(3))
                order = (F(dot(price, e), sum(e)), sum(e))
                if best is None or order > best:
                    best = order
                    next_step = (e, mask)
            result.append(next_step)
            current = next_step[1]
        return result
    return principal


def check_witness(result, edges):
    if not result.eta:
        return
    weights = [None]*6
    previous = 0
    for mask, block_weights in result.weighted_steps:
        for j in range(6):
            if (mask ^ previous) >> j & 1:
                weights[j] = block_weights[j//2]
        previous = mask
    assert previous == 63
    assert all(weights[2*i]+weights[2*i+1] == 0 for i in range(3))
    assert min(weights[j]-weights[i] for i, j in edges) == 1
    assert dot(weights, weights)*result.squared == 1


if __name__ == "__main__":
    histogram = Counter()
    max_calls = 0
    for mask in range(1, 1 << len(ARCS)):
        edges = [edge for i, edge in enumerate(ARCS) if mask & (1 << i)]
        value, calls = dual(edges)
        assert value == primal(edges), (edges, value, primal(edges))
        result = three_vertex_margin((2, 2, 2), (0, 1, 2), coordinate_principal(edges))
        assert result.squared == value
        check_witness(result, edges)
        histogram[value] += 1
        max_calls = max(calls, max_calls)
    print(f"{sum(histogram.values())} exact agreements, {len(WALLS)} candidate walls, "
          f"at most {max_calls} price-filtration queries per input.")
    print({str(x): histogram[x] for x in sorted(histogram)})
