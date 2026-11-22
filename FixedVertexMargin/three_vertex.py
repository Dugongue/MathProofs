"""Exact price search for three vertices. The caller supplies a principal-filtration routine.

principal(integer_price) returns the decreasing Harder--Narasimhan chain as pairs
(graded_dimension_vector, cumulative_flag_step). The step is an opaque object
preserved in the returned certificate. All price computations use rational arithmetic.
"""
from dataclasses import dataclass
from fractions import Fraction as F
from functools import reduce
from math import gcd, lcm


def dot(left, right):
    return sum(x * y for x, y in zip(left, right))


@dataclass
class Margin:
    squared: F
    price: tuple
    eta: F
    # Each entry contains a cumulative step and the three shifted weights.
    # At a vertex read a weight only if that step increases its subspace.
    weighted_steps: tuple
    queries: int


def principal_from_maximizer(dimensions, zero_step, full_step, maximize):
    """Build a principal-filtration routine from a subrepresentation optimizer.

    maximize(theta) returns (dimension_vector, subrepresentation) attaining
    the largest value of theta on the original input. Any maximizer suffices.
    zero_step and full_step use that routine's representation of subspaces.
    """
    dims = tuple(dimensions)
    D = sum(dims)
    lower = ((0,)*len(dims), zero_step)
    upper = (dims, full_step)

    def principal(integer_price):
        chain = []
        pending = [(lower, upper)]
        while pending:
            (f, Fstep), (g, Gstep) = pending.pop()
            diff = tuple(y-x for x, y in zip(f, g))
            slope = F(dot(diff, integer_price), sum(diff))
            theta = tuple((D+1)*(slope.denominator*x-slope.numerator)+1
                          for x in integer_price)
            e, step = maximize(theta)
            e = tuple(e)
            if e == g:
                chain.append((diff, Gstep))
            else:
                if (len(e) != len(dims) or e == f or
                    any(not a <= b <= c for a, b, c in zip(f, e, g))):
                    raise ArithmeticError("Threshold maximizer lies outside the chain interval.")
                middle = (e, step)
                pending.append((middle, (g, Gstep)))
                pending.append(((f, Fstep), middle))
        return chain
    return principal


def three_vertex_margin(dimensions, heights, principal):
    """Requires positive dimensions, a unit grading, and at least one nonzero arrow."""
    dims = tuple(dimensions)
    if len(dims) != 3 or len(heights) != 3 or any(d <= 0 for d in dims):
        raise ValueError("Three positive vertex dimensions and three heights are required.")
    mean = F(dot(dims, heights), sum(dims))
    c = tuple(mean - h for h in heights)
    r = tuple(d * x for d, x in zip(dims, c))
    C = dot(c, r)
    if not C:
        raise ValueError("A nonzero arrow with a unit height difference is required.")
    base = tuple(x / C for x in c)
    direction = tuple(dims[(i+1) % 3] * r[(i+2) % 3] -
                      dims[(i+2) % 3] * r[(i+1) % 3] for i in range(3))

    # Clear the denominators of the two affine-line vectors separately.
    # Comparing normalized slopes for e and f multiplies by |e| and |f|.
    def integer_vector(vec):
        denominator = lcm(*(x.denominator for x in vec))
        return tuple(int(x*denominator) for x in vec), denominator

    x, sx = integer_vector(base)
    y, sy = integer_vector(direction)
    D = sum(dims)
    B = max(1, 2*D**2*sy*max(map(abs, x)), 2*D**2*sx*max(map(abs, y)))

    def at(t):
        return tuple(x+t*y for x, y in zip(base, direction))

    queries = 0

    def query(t):
        nonlocal queries
        lam = at(t)
        scale = lcm(*(x.denominator for x in lam))
        raw = tuple(int(x * scale) for x in lam)
        common = reduce(gcd, raw, 0)
        blocks = tuple(principal(tuple(x // common for x in raw)))
        if not blocks or any(len(e) != 3 or min(e) < 0 or sum(e) <= 0 for e, _ in blocks):
            raise ValueError("Invalid principal filtration block.")
        if tuple(map(sum, zip(*(e for e, _ in blocks)))) != dims:
            raise ValueError("Principal filtration dimensions do not sum to the input.")
        slopes = [dot(lam, e)/sum(e) for e, _ in blocks]
        if any(a < b for a, b in zip(slopes, slopes[1:])):
            raise ValueError("Principal filtration slopes must decrease.")
        queries += 1
        aa = bb = F(0)
        for e, _ in blocks:
            u, v = dot(base, e), dot(direction, e)
            aa += v*v/sum(e)
            bb += 2*u*v/sum(e)
        return blocks, aa, bb

    def derivative(t):
        blocks, aa, bb = query(t)
        return 2*aa*t + bb, blocks

    def stationary(sample, left=None, right=None):
        blocks, aa, bb = query(sample)
        if not aa and bb:
            raise ArithmeticError("Inconsistent principal filtration quadratic.")
        t = -bb/(2*aa) if aa else sample
        if (left is not None and t < left) or (right is not None and t > right):
            raise ArithmeticError("Stationary price falls outside the selected interval.")
        return t, blocks

    # All slope-order walls lie strictly between these endpoints.
    left, right = F(-B-1), F(B+1)
    dl, left_blocks = derivative(left)
    if dl == 0:
        selected = (left, left_blocks)
    elif dl > 0:
        selected = stationary(left, right=left)
    else:
        dr, right_blocks = derivative(right)
        if dr == 0:
            selected = (right, right_blocks)
        elif dr < 0:
            selected = stationary(right, left=right)
        else:
            selected = None
            while (right-left)*2*B**2 >= 1:
                mid = (left+right)/2
                dm, blocks = derivative(mid)
                if dm == 0:
                    selected = (mid, blocks)
                    break
                if dm < 0:
                    left = mid
                else:
                    right = mid
            if selected is None:
                # At most one possible wall lies in this interval. The closest
                # bounded-denominator rational to its midpoint finds it if present.
                candidate = ((left+right)/2).limit_denominator(B)
                if left < candidate < right:
                    dc, blocks = derivative(candidate)
                    if dc == 0:
                        selected = (candidate, blocks)
                    elif dc < 0:
                        left = candidate
                    else:
                        right = candidate
                if selected is None:
                    selected = stationary((left+right)/2, left, right)

    t, blocks = selected
    lam = at(t)
    pooled = []
    eta = F(0)
    moments = [F(0)]*3
    for e, step in blocks:
        slope = dot(lam, e)/sum(e)
        eta += sum(e)*slope**2
        for i in range(3):
            moments[i] += e[i]*slope
        if pooled and pooled[-1][0] == slope:
            pooled.pop()
        pooled.append((slope, step))
    if tuple(moments) != tuple(eta*x for x in r) or C*eta >= 1:
        raise ArithmeticError("The price and filtration fail the vertex-sum certificate.")
    if not eta:
        return Margin(F(0), lam, eta, (), queries)
    steps = tuple((step, tuple(slope/eta-x for x in c)) for slope, step in pooled)
    return Margin(eta/(1-C*eta), lam, eta, steps, queries)
