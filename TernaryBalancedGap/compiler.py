"""One-instance directional-gap compiler over F3. See RESULTS.md for its domain."""
import argparse
import itertools
import json
import math
import sys

from balanced import chain_profile, factors, meet_profile, merge
from intertwiners import slice_profile


SIGNS = set(itertools.product(range(2), repeat=3))


def eliminate(rows):
    """Return RREF, pivot columns, and determinant bit of the full-row pivot minor."""
    a = [r.copy() for r in rows]
    pivots = []
    bit = 0
    for j in range(len(a[0])):
        i = len(pivots)
        s = next((s for s in range(i, len(a)) if a[s][j]), None)
        if s is None:
            continue
        if s != i:
            a[i], a[s] = a[s], a[i]
            bit ^= 1
        unit = a[i][j]
        bit ^= unit == 2
        a[i] = [(x * unit) % 3 for x in a[i]]
        for t, row in enumerate(a):
            if t != i and row[j]:
                a[t] = [(x - row[j] * y) % 3 for x, y in zip(row, a[i])]
        pivots.append(j)
        if i + 1 == len(a):
            break
    return a[:len(pivots)], pivots, int(bit)


def flatten(shape, data, order):
    m, n, k = (shape[i] for i in order)
    strides = [shape[1] * shape[2], shape[2], 1]
    x, y, z = (strides[i] for i in order)
    return [[data[i*x + j*y + t*z] for i in range(m) for j in range(n)]
            for t in range(k)]


def pack(rows):
    return [x for col in zip(*rows) for x in col]


def kernel(reduction, width):
    rows, pivots, _ = reduction
    free = sorted(set(range(width)) - set(pivots))
    basis = []
    for j in free:
        v = [0] * width
        v[j] = 1
        for p, row in zip(pivots, rows):
            v[p] = -row[j] % 3
        basis.append(v)
    return basis


def orientation(reduction):
    _, pivots, bit = reduction
    return (bit + sum(p - i for i, p in enumerate(pivots))) % 2


def matrices(n):
    for entries in itertools.product(range(3), repeat=n*n):
        rows = [list(entries[i:i+n]) for i in range(0, n*n, n)]
        _, pivots, bit = eliminate(rows)
        if len(pivots) == n:
            yield rows, bit


def multiply(a, b):
    cols = list(zip(*b))
    return [[sum(x*y for x, y in zip(row, col)) % 3 for col in cols] for row in a]


def enumerate_profile(m, n, source, target):
    # Both flattenings have full row rank. The third map is uniquely determined.
    canonical, _, source_bit = eliminate(source)
    slices = [[row[i:i+n] for i in range(0, m*n, n)] for row in target]
    found = set()
    for p, pbit in matrices(m):
        left = [multiply(p, t) for t in slices]
        for q, qbit in matrices(n):
            transformed = [sum(multiply(t, q), []) for t in left]
            basis, _, target_bit = eliminate(transformed)
            if basis == canonical:
                found.add((pbit, qbit, source_bit ^ target_bit))
            if found == SIGNS:
                return found
    return found


class Unresolved(ValueError):
    pass


def profile(shape, source, target, exhaustive=False, *, split=True, budget=None):
    if budget is None:
        budget = 2 * 3**9 + math.prod(shape)**2
    history = []
    found = None
    while found is None:
        # A largest output has the smallest product of the two other dimensions.
        largest = max(range(3), key=shape.__getitem__)
        for kaxis in [largest] + [i for i in range(3) if i != largest]:
            order = [i for i in range(3) if i != kaxis] + [kaxis]
            m, n, k = (shape[i] for i in order)
            a, b = (flatten(shape, x, order) for x in (source, target))
            ra, rb = eliminate(a), eliminate(b)
            rank = len(ra[1])
            if rank != len(rb[1]):
                return set()
            if not rank:
                found = SIGNS
                break
            if rank < k:
                history.append((order, 'support', m, n, 0))
                shape = (m, n, rank)
                source, target = pack(ra[0]), pack(rb[0])
                break
            h = m*n - k
            if h < k:
                shift = orientation(ra) ^ orientation(rb)
                history.append((order, 'kernel', m, n, shift))
                if not h:
                    found = {(p, q, 0) for p in range(2) for q in range(2)}
                    break
                shape = (m, n, h)
                source, target = pack(kernel(ra, m*n)), pack(kernel(rb, m*n))
                break
        else:
            order = [i for i in range(3) if i != largest] + [largest]
            m, n, _ = (shape[i] for i in order)
            if max(shape) >= 3:
                left = factors(shape, source, eliminate, kernel, multiply)
                right = factors(shape, target, eliminate, kernel, multiply)
                if left[2] is not None or right[2] is not None:
                    if left[2] is None or right[2] is None:
                        return set()
                    found = chain_profile(shape[0], left[2], right[2])
                    break
                if split and (len(left[0]) > 1 or len(right[0]) > 1):
                    def local(dims, a, b):
                        return profile(dims, a, b, exhaustive, split=False, budget=budget)
                    found = merge(left, right, local)
                    break
            a = flatten(shape, source, order)
            b = flatten(shape, target, order)
            if 3**(m*m) + 3**(n*n) <= budget:
                found = meet_profile(m, n, a, b, (eliminate, matrices, multiply))
            else:
                found = slice_profile(shape, source, target, budget, eliminate, matrices, kernel, flatten)
                if found is not None:
                    break  # The slice solver already reports original mode order.
                if not exhaustive:
                    raise Unresolved(f"terminal format {shape} exceeds polynomial bounds for the implemented methods")
                found = enumerate_profile(m, n, a, b)
            history.append((order, 'permute', m, n, 0))
            break
    for order, kind, m, n, shift in reversed(history):
        lifted = set()
        for p, q, t in found:
            if kind == 'support':
                bits = (0, 1)
            elif kind == 'kernel':
                bits = ((n*p + m*q + t + shift) % 2,)
            else:
                bits = (t,)
            for bit in bits:
                original = [0]*3
                for i, value in zip(order, (p, q, bit)):
                    original[i] = value
                lifted.add(tuple(original))
        found = lifted
    return found


def compile_pair(obj, exhaustive=False):
    shape = obj['shape']
    if len(shape) != 3 or any(type(n) is not int or n < 1 for n in shape):
        raise ValueError("shape must contain three positive dimensions")
    for name in ('source', 'target'):
        data = obj[name]
        if len(data) != math.prod(shape) or any(type(t) is not int or t not in (0, 1, 2) for t in data):
            raise ValueError(f"{name} must be a dense row-major list of trits")
    # Two central minus identities fix a tensor. Here their sign tuple is e1.
    forced_no = shape[0] % 2 == 1 and any(n % 2 == 0 for n in shape[1:])
    first_rank = len(eliminate(flatten(shape, obj['source'], (1, 2, 0)))[1])
    if forced_no or first_rank < shape[0] or obj['source'] == obj['target']:
        yes = False
    else:
        signs = profile(shape, obj['source'], obj['target'], exhaustive)
        yes = (1, 0, 0) in signs and (0, 0, 0) not in signs
    return {'shape': [1, 1, 1], 'source': [1], 'target': [int(yes)]}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exhaustive', action='store_true', help='enumerate remaining balanced cores (exponential)')
    args = parser.parse_args()
    try:
        print(json.dumps(compile_pair(json.load(sys.stdin), args.exhaustive)))
    except (ValueError, KeyError, TypeError) as exc:
        parser.exit(2, f"{exc}\n")
