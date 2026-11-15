"""Small-instance implementation of the Highway to Hull collision strategy.

Uses verified rank-one recovery from the linearized conjugacy system.
A failed, capped or unsupported search gives 'unknown', never 'no'.
"""
import argparse
from collections import defaultdict
import json
from pathlib import Path
from time import perf_counter

import numpy as np

from ref_io import read_pair, verify


def rref(rows, p, column_limit=None):
    rows = np.asarray(rows, dtype=np.int64).copy() % p
    _, n = rows.shape
    piv = []
    for j in range(n if column_limit is None else column_limit):
        r = len(piv)
        found = np.flatnonzero(rows[r:, j])
        if not len(found):
            continue
        h = r + int(found[0])
        rows[[r, h]] = rows[[h, r]]
        rows[r, j:] = rows[r, j:] * pow(int(rows[r, j]), -1, p) % p
        factors = rows[:, j].copy()
        factors[r] = 0
        rows[:, j:] = (rows[:, j:] - factors[:, None] * rows[None, r, j:]) % p
        piv.append(j)
        if len(piv) == rows.shape[0]:
            break
    return rows, piv


def space_rank(rows, p):
    return len(rref(rows, p)[1])


def kernel(rows, p):
    rows, piv = rref(rows, p)
    free = [i for i in range(rows.shape[1]) if i not in piv]
    basis = np.zeros((len(free), rows.shape[1]), dtype=np.int64)
    basis[np.arange(len(free)), free] = 1
    basis[:, piv] = -rows[:len(piv), free].T % p
    return basis


def characteristic(matrix, p):
    """Hessenberg similarity plus leading-minor recurrence, any characteristic."""
    h = matrix.copy()
    n = len(h)
    for j in range(n - 2):
        indices = np.flatnonzero(h[j + 1:, j])
        if not len(indices):
            continue
        r = j + 1 + int(indices[0])
        h[[r, j + 1], :] = h[[j + 1, r], :]
        h[:, [r, j + 1]] = h[:, [j + 1, r]]
        inverse = pow(int(h[j + 1, j]), -1, p)
        for i in range(j + 2, n):
            factor = int(h[i, j]) * inverse % p
            h[i, :] = (h[i, :] - factor * h[j + 1, :]) % p
            h[:, j + 1] = (h[:, j + 1] + factor * h[:, i]) % p
    polys = [np.array([1], dtype=np.int64)]
    for j in range(n):
        curr = np.pad(polys[-1], (1, 0))
        curr[:-1] -= int(h[j, j]) * polys[-1]
        coeff = 1
        for i in range(j - 1, -1, -1):
            coeff = coeff * int(h[i + 1, i]) % p
            curr[:i + 1] -= (coeff * int(h[i, j]) % p) * polys[i]
        polys.append(curr % p)
    return tuple(map(int, polys[-1]))


def trim(seq):
    seq = list(seq)
    while seq and seq[-1] == 0:
        seq.pop()
    return seq


def remainder(a, b, p):
    a = trim(a)
    inverse = pow(b[-1], -1, p)
    while len(a) >= len(b):
        shift = len(a) - len(b)
        q = a[-1] * inverse % p
        a[shift:] = [(x - q * y) % p for x, y in zip(a[shift:], b)]
        a = trim(a)
    return a


def squarefree(poly, p):
    a = list(poly)
    b = trim(i * poly[i] % p for i in range(1, len(poly)))
    while b:
        a, b = b, remainder(a, b, p)
    return len(a) == 1


def hull_anchor(code, dual, p, powers, rng):
    if not len(dual):
        return None
    k, m, n = code.shape
    selector = (rng.integers(p, size=len(dual)) @ dual % p).reshape(m, n)
    branch = code @ selector.T % p
    basis = branch.reshape(k, -1)
    gram = basis @ branch.transpose(0, 2, 1).reshape(k, -1).T % p
    h = kernel(gram, p)
    if len(h) != 1 or space_rank(basis, p) != k:
        return None
    u = (h @ basis % p).reshape(m, m)
    poly = characteristic(u, p)
    if not poly[0] or not squarefree(poly, p):
        return None
    scaled = powers * np.array(poly[:-1], dtype=np.int64) % p
    key = min(map(tuple, scaled.tolist()))
    factors = np.flatnonzero(np.all(scaled == key, axis=1)) + 1
    u_normalized = u * int(factors[0]) % p
    return key, branch, u_normalized, tuple(int(b) * pow(int(factors[0]), -1, p) % p for b in factors)


def intertwiners(u, v, p):
    """Basis for X with v X = X u in row-major coordinates."""
    eye = np.eye(len(u), dtype=np.int64)
    eq = np.kron(v, eye) - np.kron(eye, u.T)
    return kernel(eq, p).reshape(-1, len(u), len(u))


def external_right(code_a, dual_b, left, p, random):
    h, m, n = code_a.shape
    current = left @ code_a % p
    equations = np.einsum("kis,aij->kasj", current, dual_b.reshape(-1, m, n)) % p
    space = kernel(equations.reshape(h * len(dual_b), n * n), p)
    for candidate in vectors(space, p, random):
        r = candidate.reshape(n, n)
        if space_rank(r, p) == n:
            return r
    return None


def vectors(space, p, random, limit=16):
    for row in space:
        yield row
    if len(space) > 1:
        for _ in range(limit):
            yield random.integers(p, size=len(space)) @ space % p


def collision_left(a, b, u, v, p, rng, max_cells):
    # Use bases of the candidate intertwiner spaces in both directions. An
    # inverse pair is a decomposable point of the linearized nullspace.
    n = len(u)
    k = len(a)
    forward, backward = intertwiners(u, v, p), intertwiners(v, u, p)
    if len(forward) != n or len(backward) != n:
        return
    dual = kernel(b.reshape(k, -1), p)
    if n ** 4 * max(k, len(dual)) > max_cells:
        return
    product = (forward[:, None, None] @ a[None, None] % p) @ backward[None, :, None] % p
    coeff = np.einsum("ijax,bx->abij", product.reshape(n, n, k, n * n), dual) % p
    identity = forward[:, None] @ backward[None] % p
    identity = identity.reshape(n, n, n * n)
    for i in range(1, n):
        identity[:, :, i * n + i] -= identity[:, :, 0]
    equations = np.concatenate([
        coeff.reshape(-1, n * n),
        identity[:, :, 1:].transpose(2, 0, 1).reshape(-1, n * n),
    ])
    space = kernel(equations, p)
    for z in vectors(space, p, rng):
        zz = z.reshape(n, n)
        if space_rank(zz, p) == 1:
            row = next(row for row in zz if np.any(row))
            col = zz[:, int(np.flatnonzero(row)[0])]
            l = (col @ forward.reshape(n, -1) % p).reshape(n, n)
            if space_rank(l, p) == n:
                yield l


def basis_change(code_a, code_b, left, right, p):
    k = len(code_a)
    reduce, piv = rref(
        np.concatenate([code_b.reshape(k, -1), np.eye(k, dtype=np.int64)], axis=1),
        p, code_b[0].size,
    )
    if len(piv) != k:
        return None
    moved = (left @ code_a % p) @ right % p
    coeff = moved.reshape(k, -1)[:, piv] @ reduce[:, code_b[0].size:] % p
    if np.array_equal(coeff @ code_b.reshape(k, -1) % p, moved.reshape(k, -1)):
        return coeff
    return None


def solve(path, seed, attempts, timeout, dualize, max_cells):
    begin = perf_counter()
    p, m, n, k, a_raw, b_raw = read_pair(path)
    read = perf_counter()
    result = {"case": path.name, "format": [p, m, n, k], "backend": "Highway to Hull adaptation (NumPy)",
              "result": "unknown", "seed": seed}
    if p > 65521 or max(m, n, k) > 512:
        result["reason"] = "experimental arithmetic cap"
        return result
    transposed = m > n
    a, b = np.array(a_raw, dtype=np.int64), np.array(b_raw, dtype=np.int64)
    if transposed:
        a, b = a.transpose(0, 2, 1), b.transpose(0, 2, 1)
        m, n = n, m
    if space_rank(a.reshape(k, -1), p) != k or space_rank(b.reshape(k, -1), p) != k:
        result["reason"] = "input bases must be independent"
        return result
    da, db = kernel(a.reshape(k, -1), p), kernel(b.reshape(k, -1), p)
    if dualize:
        ca, cb = da.reshape(-1, m, n), db.reshape(-1, m, n)
        cda, cdb = a.reshape(k, -1), b.reshape(k, -1)
    else:
        ca, cb, cda, cdb = a, b, da, db
    powers = np.array([[pow(c, m - i, p) for i in range(m)] for c in range(1, p)],
                      dtype=np.int64)
    rng = np.random.default_rng(seed)
    tables = [defaultdict(list), defaultdict(list)]
    anchors = [0, 0]
    matches = 0
    ready = perf_counter()
    tested = 0
    result["reason"] = "sample budget"
    for idx in range(attempts):
        if perf_counter() - begin > timeout:
            result["reason"] = "time budget"
            break
        side = idx % 2
        tested += 1
        code, comp = (ca, cda) if side == 0 else (cb, cdb)
        sample = hull_anchor(code, comp, p, powers, rng)
        if sample is None:
            continue
        key, branch, marker, scales = sample
        anchors[side] += 1
        for other_branch, other_marker, other_scales in tables[1 - side].get(key, ()):
            matches += 1
            if side == 0:
                sa, sb, ua, ub, scalars = branch, other_branch, marker, other_marker, other_scales
            else:
                sa, sb, ua, ub, scalars = other_branch, branch, other_marker, marker, scales
            for scalar in scalars:
                for left in collision_left(sa, sb, ua, ub * scalar % p, p, rng, max_cells):
                    candidate_hull = basis_change(sa, sb, left, inverse(left, p), p)
                    if candidate_hull is None:
                        continue
                    right = external_right(ca, cdb, left, p, rng)
                    if right is None:
                        continue
                    if dualize:
                        left, right = inverse(left, p).T, inverse(right, p).T
                    mix = basis_change(a, b, left, right, p)
                    if mix is None:
                        continue
                    if transposed:
                        left, right = right.T, left.T
                    output = [left.tolist(), right.tolist(), mix.tolist()]
                    after_search = perf_counter()
                    if not verify(p, len(a_raw[0]), len(a_raw[0][0]), k, a_raw, b_raw, *output):
                        raise AssertionError("Hull witness does not satisfy the original input")
                    end = perf_counter()
                    result.update(result="yes", anchors=anchors, collisions=matches, attempts=tested,
                                  read_ms=1000 * (read - begin), build_ms=1000 * (ready - read),
                                  search_ms=1000 * (after_search - ready), verify_ms=1000 * (end - after_search),
                                  total_ms=1000 * (end - begin))
                    result.pop("reason", None)
                    return result | dict(zip(("left", "right", "mixing"), output))
        bucket = tables[side][key]
        if len(bucket) < 24:
            bucket.append((branch, marker, scales))
    end = perf_counter()
    result.update(anchors=anchors, collisions=matches, attempts=tested,
                  read_ms=1000 * (read - begin), build_ms=1000 * (ready - read),
                  search_ms=1000 * (end - ready), total_ms=1000 * (end - begin))
    return result


def inverse(matrix, p):
    n = len(matrix)
    red, piv = rref(np.concatenate([matrix, np.eye(n, dtype=np.int64)], axis=1), p, n)
    if len(piv) != n:
        raise ValueError("Expected invertible matrix")
    return red[:, n:]


if __name__ == "__main__":
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("cases", nargs="+", type=Path)
    args.add_argument("--samples", type=int, default=512)
    args.add_argument("--timeout", type=float, default=5)
    args.add_argument("--seed", type=int, default=1)
    args.add_argument("--dual", action="store_true")
    args.add_argument("--max-cells", type=int, default=2_000_000)
    opt = args.parse_args()
    for path in opt.cases:
        print(json.dumps(solve(path, opt.seed, opt.samples, opt.timeout, opt.dual, opt.max_cells)),
              flush=True)
