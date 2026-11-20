"""Exact finite controls for the polynomial separator and torus degree proof."""
from fractions import Fraction as Q
from itertools import product

I = (1, 0, 0, 1)
ZERO = (0, 0, 0, 0)
ORDER = 3


def mm(u, v):
    a, b, c, d = u
    e, f, g, h = v
    return (a*e+b*g, a*f+b*h, c*e+d*g, c*f+d*h)


def multiply_series(a, b):
    result = [[Q(0)]*4 for _ in range(ORDER + 1)]
    for i, u in enumerate(a):
        for j in range(ORDER + 1 - i):
            for k, entry in enumerate(mm(u, b[j])):
                result[i+j][k] += entry
    return result


def exp_series(direction, rate):
    out = [ZERO for _ in range(ORDER + 1)]
    out[0] = term = I
    for k in range(1, ORDER // rate + 1):
        term = tuple(Q(t, k) for t in mm(term, direction))
        out[k*rate] = term
    return out


def direction(label, scale=1):
    a, b = label
    return (0, scale*a, scale*b, 0)


def witness_product(a, b, bp, c, hx):
    x = exp_series(direction(a), 2)
    yn = exp_series(direction(b, -1), 1)
    yp = exp_series(direction(bp), 1)
    zn = exp_series(direction(c, -hx), 2)
    return multiply_series(multiply_series(multiply_series(x, yn), yp), zn)


def selector_leading(coeffs, grid, target, divisor):
    """Return a certified lower bound on order and leading term if known."""
    order = 0
    leading = Q(1)
    for other in grid:
        if other == target:
            continue
        factor = dict((j-divisor, c) for j, c in enumerate(coeffs) if c)
        factor[0] = factor.get(0, Q(0)) - other
        active = [(j, c) for j, c in factor.items() if c]
        if not active:
            order += ORDER + 1 - divisor
            leading = None
        else:
            exponent, value = min(active)
            order += exponent
            if leading is not None:
                leading *= value / (target-other)
    return order, leading


def check_noncommutative_grid(hx, hy, hz):
    ax = list(product(range(hx), repeat=2))
    by = list(product(range(hy), repeat=2))
    cz = list(product(range(hz), repeat=2))
    hi = range(1-hy, hy)
    lo = range(-hx*(hz-1), hx)
    degree = len(lo)-1
    counts = dict(clean_output=0, other_output=0, noisy_support=0)
    for a, b, bp, c in product(ax, by, by, cz):
        g = witness_product(a, b, bp, c, hx)
        assert tuple(g[0]) == I
        jets = [[row[i] for row in g] for i in (1, 2)]
        assert [jet[1] for jet in jets] == [bp[0]-b[0], bp[1]-b[1]]
        gates = [selector_leading(jet, hi, 0, 1) for jet in jets]
        for target_a, target_c in product(ax, cz):
            order = 0
            coefficient = Q(1)
            for i, jet in enumerate(jets):
                w = target_a[i]-hx*target_c[i]
                ov, cv = selector_leading(jet, lo, w, 2)
                og, cg = gates[i]
                order += ov + (degree+1)*og
                coefficient = (coefficient * cv * cg**(degree+1)
                    if None not in (coefficient, cv, cg) else None)
            if b != bp:
                assert order >= 1
                counts["noisy_support"] += 1
            elif a == target_a and c == target_c:
                assert order == 0 and coefficient == 1
                counts["clean_output"] += 1
            else:
                assert order >= 1
                counts["other_output"] += 1
    return counts


def check_torus_vandermonde(hx, hy, hz):
    hi = range(1-hy, hy)
    lo = range(-hx*(hz-1), hx)
    labels = list(product(hi, lo))
    count = len(labels)
    e = Q(1, 10*count)
    mixed = {u+hx*hz*b for b, u in labels}
    assert len(mixed) == count and max(mixed)-min(mixed) == count-1
    points = [1 + e*b + e*e*u for b, u in labels]
    weights = []
    limits = []
    for i, (b,u) in enumerate(labels):
        w = Q(1)
        lead = 1
        valuation = 0
        for j, (c,v) in enumerate(labels):
            if j == i:
                continue
            w *= points[i]-points[j]
            if b != c:
                valuation += 1
                lead *= b-c
            else:
                valuation += 2
                lead *= u-v
        assert w and lead and valuation == count + len(lo)-2
        weights.append(1/w)
        limits.append(Q(1,lead))
    assert all(limits)
    for power in range(count):
        moment = sum(weight * point**power for weight, point in zip(weights, points))
        assert moment == int(power == count-1)
    return count-1


def main():
    for sizes in ((2,2,2), (3,2,2), (2,3,2)):
        record = check_noncommutative_grid(*sizes)
        degree = check_torus_vandermonde(*sizes)
        print(sizes, record, "sharp scalar degree", degree)


if __name__ == "__main__":
    main()
