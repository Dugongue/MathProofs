"""Exact SL-TI witnesses for regular rational pencils with <=2 rational roots.

Read {"A": [Ax, Ay], "B": [Bx, By]} on stdin. Matrix entries may be integers
or fraction strings. Run --self-test for deterministic positive and negative
fixtures. Out-of-scope inputs return "unsupported".
"""

import argparse
from collections import deque
from fractions import Fraction as F
from functools import reduce
import json
from math import gcd
from random import Random
import sys


def eye(n):
    return [[F(i == j) for j in range(n)] for i in range(n)]


def mul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def combination(a, b, x, y):
    return [[x*u + y*v for u, v in zip(row, col)] for row, col in zip(a, b)]


def rref(matrix):
    a = [row.copy() for row in matrix]
    pivots = []
    det = F(1)
    for j in range(len(a[0])):
        k = len(pivots)
        i = next((i for i in range(k, len(a)) if a[i][j]), None)
        if i is None:
            continue
        if i != k:
            a[k], a[i] = a[i], a[k]
            det = -det
        pivot = a[k][j]
        det *= pivot
        a[k] = [v/pivot for v in a[k]]
        for i, row in enumerate(a):
            if i != k and row[j]:
                a[i] = [x-row[j]*y for x, y in zip(row, a[k])]
        pivots.append(j)
        if len(pivots) == len(a):
            break
    return a, pivots, det


def determinant(a):
    _, pivots, det = rref(a)
    return det if len(pivots) == len(a) else F(0)


def inv(a):
    n = len(a)
    b, pivots, _ = rref([row + unit for row, unit in zip(a, eye(n))])
    assert pivots == list(range(n))
    return [row[n:] for row in b]


def nullspace(a):
    b, pivots, _ = rref(a)
    for j in range(len(a[0])):
        if j in pivots:
            continue
        vector = [F(0)]*len(a[0])
        vector[j] = F(1)
        for i, pivot in enumerate(pivots):
            vector[pivot] = -b[i][j]
        yield vector


def block_diag(blocks):
    size = sum(map(len, blocks))
    result = [[F(0)]*size for _ in range(size)]
    offset = 0
    for block in blocks:
        for i, row in enumerate(block):
            result[offset+i][offset:offset+len(block)] = row
        offset += len(block)
    return result


def jordan(n):
    return [[F(j == i+1) for j in range(n)] for i in range(n)]


def integer_root(x, n):
    low, high = 0, 1 << ((x.bit_length()+n-1)//n)
    while low < high:
        mid = (low+high+1)//2
        if mid**n <= x:
            low = mid
        else:
            high = mid-1
    return low if low**n == x else None


def exact_root(x, n):
    if n == 0:
        return F(1) if x == 1 else None
    if n < 0:
        return exact_root(1/x, -n)
    if x < 0 and n % 2 == 0:
        return None
    numerator = integer_root(abs(x.numerator), n)
    denominator = integer_root(x.denominator, n)
    if numerator is None or denominator is None:
        return None
    return F(-numerator if x < 0 else numerator, denominator)


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def divmod_poly(p, q):
    p = p.copy()
    quotient = [F(0)]*max(0, len(p)-len(q)+1)
    while len(p) >= len(q):
        offset = len(p)-len(q)
        ratio = p[-1]/q[-1]
        quotient[offset] = ratio
        for j, coeff in enumerate(q):
            p[offset+j] -= ratio*coeff
        trim(p)
    return quotient, p


def eigenvalues(c):
    n = len(c)
    identity = eye(n)
    m = identity
    coeffs = [F(1)]
    for d in range(1, n+1):
        cm = mul(c, m)
        coeff = -sum(cm[i][i] for i in range(n))/d
        coeffs.append(coeff)
        m = combination(cm, identity, 1, coeff)
    p = coeffs[::-1]
    a, b = p, [j*p[j] for j in range(1, len(p))]
    while b:
        _, rem = divmod_poly(a, b)
        a, b = b, rem
    q, _ = divmod_poly(p, a)
    if len(q) == 2:
        return [-q[0]/q[1]]
    if len(q) == 3:
        a, b, c = q[::-1]
        root = exact_root(b*b-4*a*c, 2)
        if root is not None:
            return sorted([(-b-root)/(2*a), (-b+root)/(2*a)])
    raise ValueError("requires one or two geometric roots, all rational")


def primary_chains(c, eigenvalue):
    n = len(c)
    nilpotent = combination(c, eye(n), 1, -eigenvalue)
    powers = [eye(n)]
    for _ in range(n):
        powers.append(mul(powers[-1], nilpotent))
    ends = []
    blocks = []
    for length in range(n, 0, -1):
        for vector in nullspace(powers[length]):
            result = mul(powers[length-1], [[x] for x in vector])
            end = [row[0] for row in result]
            if len(rref(ends + [end])[1]) == len(ends):
                continue
            ends.append(end)
            chain = []
            for j in range(length-1, -1, -1):
                result = mul(powers[j], [[x] for x in vector])
                chain.append([row[0] for row in result])
            blocks.append(chain)
    return blocks


def block_map(length, a, b, c):
    one = eye(length)
    nilpotent = jordan(length)
    unit = combination(one, nilpotent, a, b)
    moved = mul(combination(nilpotent, one, c, 0), inv(unit))
    current = [[row[-1]] for row in one]
    columns = []
    for _ in range(length):
        columns.append([row[0] for row in current])
        current = mul(moved, current)
    p = inv([list(row) for row in zip(*reversed(columns))])
    return p, mul(p, unit)


def decompose(pencil):
    x, y = pencil
    n = len(x)
    for i in range(n+1):
        base = combination(x, y, 1, i)
        if determinant(base):
            break
    else:
        raise ValueError("the determinant polynomial vanishes")
    base_inv = inv(base)
    c = mul(base_inv, y)
    s, t = [F(1), F(0)], [F(-i), F(1)]
    roots = eigenvalues(c)
    linear_forms = [[a + e*b for a, b in zip(s, t)] for e in roots]
    return base_inv, t, linear_forms, [primary_chains(c, e) for e in roots]


def canonicalize(decomposed, order):
    base_inv, t, forms, chains = decomposed
    frame = [forms[i].copy() for i in order]
    if len(frame) == 1:
        frame.append(t)
    else:
        determinant_frame = determinant(frame)
        frame[1] = [x/determinant_frame for x in frame[1]]
    local_frames = [frame, [frame[1], [-x for x in frame[0]]]]
    p_blocks, q_blocks, columns, lengths = [], [], [], []
    for k, i in enumerate(order):
        a, z = mul([forms[i]], inv(local_frames[k]))[0]
        b, c = mul([t], inv(local_frames[k]))[0]
        assert not z
        lengths.append([len(block) for block in chains[i]])
        for block in chains[i]:
            p, q = block_map(len(block), a, b, c)
            p_blocks.append(p)
            q_blocks.append(q)
            columns.extend(block)
    similarity = [list(row) for row in zip(*columns)]
    similarity_inv = inv(similarity)
    p = mul(mul(block_diag(p_blocks), similarity_inv), base_inv)
    q = mul(block_diag(q_blocks), similarity_inv)
    return frame, lengths, p, q


def correction_exponents(lengths, g):
    modulus = lengths[0]
    parents = {0: None}
    pending = deque([0])
    target = g % modulus
    while target not in parents:
        residue = pending.popleft()
        for i, size in enumerate(lengths[1:], 1):
            new_residue = (residue+size) % modulus
            if new_residue not in parents:
                parents[new_residue] = residue, i
                pending.append(new_residue)
    exponents = [0]*len(lengths)
    while target:
        target, i = parents[target]
        exponents[i] += 1
    total = sum(r*l for r, l in zip(exponents, lengths))
    exponents[0] = (g-total)//modulus
    return exponents


def check_witness(a, b, witness):
    p, q, r = (witness[key] for key in ("P", "Q", "R"))
    return all(determinant(m) == 1 for m in (p, q, r)) and all(
        mul(p, combination(*a, *coeffs)) == mul(bi, q)
        for coeffs, bi in zip(zip(*r), b)
    )


def solve(a, b):
    if len(a[0]) != len(b[0]):
        return {"status": "no"}
    try:
        da, db = decompose(a), decompose(b)
    except ValueError as error:
        return {"status": "unsupported", "reason": str(error)}
    k = len(da[2])
    if k != len(db[2]):
        return {"status": "no"}
    order = list(range(k))
    fa, expected_lengths, pa, qa = canonicalize(da, order)
    for target_order in [order] if k == 1 else [order, order[::-1]]:
        fb, lengths, pb, qb = canonicalize(db, target_order)
        if expected_lengths != lengths:
            continue
        sizes = sum(lengths, [])
        g = reduce(gcd, sizes)
        n = sum(sizes)
        d = n if k == 1 else sum(lengths[0])-sum(lengths[1])
        p0, q0 = determinant(pb)/determinant(pa), determinant(qb)/determinant(qa)
        a0 = exact_root(q0/p0, d)
        if a0 is None or exact_root(p0, g) is None:
            continue
        r = mul(mul(inv(fa), [[a0, F(0)], [F(0), 1/a0]]), fb)
        p_blocks, q_blocks = [], []
        for group, dilation in zip(lengths, (a0, 1/a0)):
            for ell in group:
                p, q = block_map(ell, dilation, F(0), 1/dilation)
                p_blocks.append(p)
                q_blocks.append(q)
        pc, qc = block_diag(p_blocks), block_diag(q_blocks)
        t = exact_root(p0/determinant(pc), g)
        assert t is not None
        powers = correction_exponents(sizes, g)
        strict = block_diag([combination(eye(ell), eye(ell), t**pow0, 0)
                             for ell, pow0 in zip(sizes, powers)])
        witness = {
            "status": "yes",
            "P": mul(mul(inv(pb), mul(strict, pc)), pa),
            "Q": mul(mul(inv(qb), mul(strict, qc)), qa),
            "R": r,
        }
        assert check_witness(a, b, witness)
        return witness
    return {"status": "no"}


def pencil(*groups):
    blocks = [(eye(ell), jordan(ell)) for ell in groups[0]]
    if len(groups) == 2:
        for ell in groups[1]:
            nilpotent = jordan(ell)
            blocks.append((combination(nilpotent, nilpotent, -1, 0), eye(ell)))
    return [block_diag(items) for items in zip(*blocks)]


def random_sl(n, rng):
    a = eye(n)
    for _ in range(3*n):
        i, j = rng.sample(range(n), 2)
        t = F(rng.randrange(-5, 6), rng.randrange(1, 5))
        a[i] = [x+t*y for x, y in zip(a[i], a[j])]
    return a


def self_test():
    rng = Random(421)
    count = 0
    for groups in [([4, 2],), ([3, 2],), ([2, 1], [2]), ([2], [2]),
                   ([3, 1], [2, 2]), ([4], [2]), ([1], [1])]:
        a = pencil(*groups)
        n = len(a[0])
        for i in range(3):
            p, q = [random_sl(n, rng) for _ in range(2)]
            r = random_sl(2, rng) if i < 2 else [[F(0), F(-1)], [F(1), F(0)]]
            b = [mul(mul(p, combination(*a, *v)), inv(q)) for v in zip(*r)]
            found = solve(a, b)
            assert found["status"] == "yes"
            assert check_witness(a, b, found)
            count += 1
    no_split = pencil([2])
    d = [[F(2), F(0)], [F(0), F(1)]]
    conjugates = [mul(mul(d, item), inv(d)) for item in no_split]
    assert solve(no_split, conjugates)["status"] == "no"
    count += 1
    balanced = pencil([2], [2])
    d = block_diag([d, eye(2)])
    assert solve(balanced, [mul(d, item) for item in balanced])["status"] == "no"
    count += 1
    assert solve(pencil([2]), pencil([1, 1]))["status"] == "no"
    count += 1
    unsupported = pencil([1, 1])
    unsupported[1] = [[F(0), F(1)], [F(-1), F(0)]]
    assert solve(unsupported, unsupported)["status"] == "unsupported"
    print(f"{count} decision fixtures passed, plus a nonsplit scope check")


def read_pencil(pencil_data):
    if len(pencil_data) != 2 or not len(pencil_data[0]):
        raise ValueError("requires a nonempty square binary pencil")
    n = len(pencil_data[0])
    if any(len(a) != n or any(len(row) != n for row in a) for a in pencil_data):
        raise ValueError("requires a nonempty square binary pencil")
    return [[[F(x) for x in row] for row in a] for a in pencil_data]


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    options = parser.parse_args()
    if options.self_test:
        self_test()
    else:
        problem = json.load(sys.stdin)
        print(json.dumps(solve(read_pencil(problem["A"]), read_pencil(problem["B"])),
                         default=str))
