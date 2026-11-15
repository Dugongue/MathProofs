"""Prime-field matrix-code equivalence using projective rank invariants."""

from argparse import ArgumentParser
from collections import Counter
from itertools import product
from math import isqrt
from pathlib import Path
from time import perf_counter
import json

import numpy as np


def native_backend():
    import ctypes
    import sys

    name = "mce_kernels.dll" if sys.platform == "win32" else "libmce_kernels.so"
    path = Path(__file__).with_name(name)
    if not path.exists():
        return None, None
    try:
        handle = ctypes.CDLL(str(path))
    except OSError:
        return None, None
    fn = handle.mce_rank_words
    fn.argtypes = [
        *([ctypes.c_int] * 5),
        np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS"),
        np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS"),
        np.ctypeslib.ndpointer(dtype=np.int16, flags="C_CONTIGUOUS"),
    ]
    fn.restype = None
    rref = handle.mce_rref
    rref.argtypes = [
        *([ctypes.c_int] * 4),
        np.ctypeslib.ndpointer(dtype=np.int64, flags="C_CONTIGUOUS"),
        np.ctypeslib.ndpointer(dtype=np.int32, flags="C_CONTIGUOUS"),
    ]
    rref.restype = ctypes.c_int
    return fn, rref


NATIVE_RANK_WORDS, NATIVE_RREF = native_backend()


def read_pair(path):
    tokens = path.read_bytes().split()
    if len(tokens) < 4:
        raise ValueError("Expected p, m, n, k and two matrix bases")
    p, m, n, k = map(int, tokens[:4])
    if p < 2 or p > 65521 or any(p % q == 0 for q in range(2, isqrt(p) + 1)):
        raise ValueError("Use a prime field of characteristic at most 65521")
    if not (1 <= m <= 128 and 1 <= n <= 128 and 1 <= k <= m * n):
        raise ValueError("Unsupported dimensions")
    if len(tokens) != 4 + 2 * m * n * k:
        raise ValueError("Coefficient count differs from the declared format")
    flat = np.array(list(map(int, tokens[4:])), dtype=np.int64)
    if np.any(flat < 0) or np.any(flat >= p):
        raise ValueError("Use coefficients from 0 through p-1")
    a, b = flat.reshape(2, k, m, n)
    return p, a, b


def echelon(matrix, p, search_cols=None, native=True):
    a = np.array(matrix, dtype=np.int64, copy=True, order="C")
    pivots = []
    columns = a.shape[1] if search_cols is None else search_cols
    if native and NATIVE_RREF and a.size:
        ids = np.empty(min(len(a), columns), dtype=np.int32)
        rank_value = NATIVE_RREF(p, *a.shape, columns, a, ids)
        return a, ids[:rank_value].tolist()
    for col in range(columns):
        row = len(pivots)
        nz = np.flatnonzero(a[row:, col])
        if not len(nz):
            continue
        src = row + nz[0]
        a[[row, src]] = a[[src, row]]
        a[row, col:] = a[row, col:] * pow(int(a[row, col]), -1, p) % p
        nonzero = np.flatnonzero(a[:, col])
        active = nonzero[nonzero != row]
        if len(active):
            a[active, col:] = (a[active, col:] - a[active, col, None] * a[row, col:]) % p
        pivots.append(col)
        if len(pivots) == len(a):
            break
    return a, pivots


def rank(matrix, p):
    return len(echelon(matrix, p)[1])


def inverse(matrix, p):
    n = len(matrix)
    out, pivots = echelon(np.hstack((matrix, np.eye(n, dtype=np.int64))), p, n)
    return out[:, n:] if len(pivots) == n else None


def kernel(matrix, p):
    rref, pivots = echelon(matrix, p)
    n = matrix.shape[1]
    pivot_set = set(pivots)
    free = [i for i in range(n) if i not in pivot_set]
    basis = np.zeros((len(free), n), dtype=np.int64)
    basis[np.arange(len(free)), free] = 1
    if pivots:
        basis[:, pivots] = -rref[:len(pivots), free].T % p
    return basis


def verify(a, b, p, l, r, s):
    """Convention: L A_i = (sum_j S[j,i] B_j) R for every i."""
    k, m, n = a.shape
    if l.shape != (m, m) or r.shape != (n, n) or s.shape != (k, k):
        return False
    if (rank(l, p), rank(r, p), rank(s, p)) != (m, n, k):
        return False
    images = (s.T @ b.reshape(k, m * n) % p).reshape(k, m, n)
    return np.array_equal(l @ a % p, images @ r % p)


def projective(p, k, cap):
    total = 0
    size = 1
    for _ in range(k):
        total += size
        if total > cap:
            return None
        size *= p
    result = np.zeros((total, k), dtype=np.int64)
    start = 0
    for first in range(k - 1, -1, -1):
        count = p ** (k - 1 - first)
        block = result[start:start + count]
        block[:, first] = 1
        digits = np.arange(count, dtype=np.int64)
        for col in range(k - 1, first, -1):
            block[:, col] = digits % p
            digits //= p
        start += count
    return result


def rank_word_table(a, points, p, native=True):
    k, m, n = a.shape
    size = max(1, min(4096, 2_000_000 // (m * n)))
    results = np.empty(len(points), dtype=np.int16)
    if native and NATIVE_RANK_WORDS:
        NATIVE_RANK_WORDS(p, k, m, n, len(points),
                          np.ascontiguousarray(a), np.ascontiguousarray(points), results)
        return results
    inv = np.array([0] + [pow(i, -1, p) for i in range(1, p)], dtype=np.int64)
    rows = np.arange(m)
    for start in range(0, len(points), size):
        mat = (points[start:start + size] @ a.reshape(k, m * n) % p).reshape(-1, m, n)
        ranks = np.zeros(len(mat), dtype=np.int64)
        for j in range(n):
            eligible = (rows >= ranks[:, None]) & (mat[:, :, j] != 0)
            which = np.flatnonzero(eligible.any(axis=1))
            if len(which) == 0:
                continue
            pivots = eligible[which].argmax(axis=1)
            dest = ranks[which]
            tmp = mat[which, pivots].copy()
            mat[which, pivots] = mat[which, dest]
            mat[which, dest] = tmp
            piv = tmp * inv[tmp[:, j], None] % p
            multiplier = mat[which, :, j] * (rows > dest[:, None])
            mat[which, :, j:] = (mat[which, :, j:] - multiplier[:, :, None] * piv[:, None, j:]) % p
            ranks[which] += 1
        results[start:start + len(ranks)] = ranks
    return results


def colorize(a, b):
    merged = np.vstack((a, b))
    bounds = merged.max(axis=0).astype(object) + 1
    volume = 1
    weights = []
    for bound in bounds:
        weights.append(volume)
        volume *= bound
    if volume < (1 << 63):
        _, labels = np.unique(merged @ np.array(weights, dtype=np.int64), return_inverse=True)
    else:
        _, labels = np.unique(merged, axis=0, return_inverse=True)
    return labels[:len(a)], labels[len(a):]


def joint_point_colors(points, ax, bx, ac, bc, p, rounds):
    if len(points) * len(ax) > 12_000_000:
        return ac, bc, "rank_only"
    ai = points @ ax.T % p == 0
    bi = points @ bx.T % p == 0
    for _ in range(rounds):
        palette = np.union1d(ac, bc)
        ah = np.stack([ai[:, ac == color].sum(axis=1) for color in palette], axis=1)
        bh = np.stack([bi[:, bc == color].sum(axis=1) for color in palette], axis=1)
        al, bl = colorize(ah, bh)
        if not np.array_equal(np.bincount(al, minlength=max(al.max(), bl.max()) + 1),
                              np.bincount(bl, minlength=max(al.max(), bl.max()) + 1)):
            return ac, bc, "incompatible"
        width = int(max(al.max(), bl.max())) + 1
        ash = [np.bincount(al[ai[:, i]], minlength=width) for i in range(len(ax))]
        bsh = [np.bincount(bl[bi[:, i]], minlength=width) for i in range(len(bx))]
        new_a, new_b = colorize(np.column_stack((ac, ash)), np.column_stack((bc, bsh)))
        if Counter(new_a) != Counter(new_b):
            return new_a, new_b, "incompatible"
        if len(set(new_a)) == len(set(ac)):
            break
        ac, bc = new_a, new_b
        if len(set(ac)) == len(ac):
            break
    return ac, bc, "refined"


def normalize(rows, p):
    result = rows.copy()
    nonzero = np.any(result, axis=1)
    values = result[nonzero]
    if len(values):
        first = (values != 0).argmax(axis=1)
        factors = np.array([pow(int(x), -1, p) for x in values[np.arange(len(values)), first]])
        result[nonzero] = values * factors[:, None] % p
    return result


def codeword_preserved(transform, ax, bx, ac, bc, p):
    images = normalize(ax @ transform.T % p, p)
    match = {tuple(vector): color for vector, color in zip(bx, bc)}
    return all(match.get(tuple(vector)) == color for vector, color in zip(images, ac))


def coefficient_maps(ax, bx, ac, bc, p, cap):
    """Yield all compatible projectivities or report that the cap was reached."""
    k = ax.shape[1]
    groups = {int(color): np.flatnonzero(bc == color) for color in np.unique(bc)}
    order = sorted(range(len(ax)), key=lambda i: len(groups[int(ac[i])]))
    ids = []
    for idx in order:
        if rank(ax[ids + [idx]], p) > len(ids):
            ids.append(idx)
        if len(ids) == k:
            break
    if len(ids) != k:
        return False, 0, []
    ai = inverse(ax[ids].T, p)
    old_coords = ax @ ai.T % p
    choices = [groups[int(ac[idx])] for idx in ids]
    singleton = [(i, int(groups[int(ac[i])][0])) for i in range(len(ax))
                 if len(groups[int(ac[i])]) == 1 and i not in ids]
    results = []
    visits = 0
    bases = 0
    for picked in product(*choices):
        bases += 1
        if bases > cap:
            return False, visits, results
        if len(set(picked)) != k:
            continue
        base = bx[list(picked)].T
        inv_b = inverse(base, p)
        if inv_b is None:
            continue
        relative = [[] for _ in range(k)]
        consistent = True
        for ai_idx, bi_idx in singleton:
            u = old_coords[ai_idx]
            v = inv_b @ bx[bi_idx] % p
            nonzero = np.flatnonzero(u)
            if not np.array_equal(u != 0, v != 0):
                consistent = False
                break
            h = int(nonzero[0])
            for j in nonzero[1:]:
                ratio = int(v[j]) * pow(int(u[j]), -1, p) * int(u[h]) * pow(int(v[h]), -1, p) % p
                relative[h].append((int(j), ratio))
                relative[int(j)].append((h, pow(ratio, -1, p)))
        if not consistent:
            continue
        cmp = [-1] * k
        weights = np.zeros(k, dtype=np.int64)
        pieces = 0
        for start in range(k):
            if cmp[start] >= 0:
                continue
            cmp[start] = pieces
            weights[start] = 1
            queue = [start]
            for idx in queue:
                for neighbor, scale in relative[idx]:
                    value = int(weights[idx]) * scale % p
                    if cmp[neighbor] < 0:
                        cmp[neighbor] = pieces
                        weights[neighbor] = value
                        queue.append(neighbor)
                    elif weights[neighbor] != value:
                        consistent = False
            pieces += 1
        if not consistent:
            continue
        for relatives in product(range(1, p), repeat=pieces - 1):
            visits += 1
            if visits > cap:
                return False, visits, results
            weights_k = weights * np.array((1, *relatives))[cmp] % p
            transform = (base * weights_k) @ ai % p
            if codeword_preserved(transform, ax, bx, ac, bc, p):
                results.append(transform)
    return True, visits, results


def sparse_unit(kernel_basis, m, n, p, max_combinations, rng, lift=None, fixed_l=None):
    """Return (witness or None, exhaustive). A supplied lift is linear."""
    d = len(kernel_basis)
    if d == 0:
        return None, True

    def maps(vector):
        if fixed_l is not None:
            return fixed_l, vector.reshape(n, n)
        if lift is not None:
            return lift(vector)
        return vector[:m * m].reshape(m, m), vector[m * m:].reshape(n, n)

    explicit = [maps(vector) for vector in kernel_basis]
    left, right = [np.stack(a) for a in zip(*explicit)]
    for l, r in explicit:
        if rank(r, p) == n and (fixed_l is not None or rank(l, p) == m):
            return (l, r), True
    if rank(right.reshape(d * n, n), p) < n or rank(right.transpose(0, 2, 1).reshape(d * n, n), p) < n:
        return None, True
    candidates = projective(p, d, max_combinations)
    complete = candidates is not None
    if candidates is None:
        candidates = rng.integers(0, p, size=(80, d), dtype=np.int64)
    valid = np.flatnonzero(rank_word_table(right, candidates, p) == n)
    if fixed_l is None and len(valid):
        valid = valid[rank_word_table(left, candidates[valid], p) == m]
    if not len(valid):
        return None, complete
    vector = candidates[valid[0]] @ kernel_basis % p
    return maps(vector), True


def cyclic_equations(a, b, p):
    """If a shared slice is invertible and the source has a cyclic vector."""
    k, m, n = a.shape
    if m != n:
        return None
    for a0, b0 in zip(a, b):
        a_inv, b_inv = inverse(a0, p), inverse(b0, p)
        if a_inv is not None and b_inv is not None:
            break
    else:
        return None
    c = a @ a_inv % p
    d = b @ b_inv % p
    eye = np.eye(n, dtype=np.int64)
    for basis_vec in eye[:min(4, n)]:
        words = [(basis_vec, eye)]
        reduced = []
        pivots = []

        def add(v):
            x = v.copy()
            for row, col in zip(reduced, pivots):
                x = (x - x[col] * row) % p
            support = np.flatnonzero(x)
            if not len(support):
                return False
            idx = int(support[0])
            reduced.append(x * pow(int(x[idx]), -1, p) % p)
            pivots.append(idx)
            return True

        add(basis_vec)
        for x, w in words:
            if len(words) == n:
                break
            for ci, di in zip(c, d):
                y = ci @ x % p
                if add(y):
                    words.append((y, di @ w % p))
                    if len(words) == n:
                        break
        if len(words) == n:
            break
    else:
        return None
    x_inv = inverse(np.stack([x for x, _ in words], axis=1), p)
    operators = np.stack([w for _, w in words])
    x_space = np.stack([x for x, _ in words], axis=1)
    relations = []
    for ci, di in zip(c, d):
        for j in range(n):
            relation = x_inv @ (ci @ x_space[:, j] % p) % p
            term = relation @ operators.reshape(n, n * n) % p
            relations.append((di @ operators[j] - term.reshape(n, n)) % p)
    matrix = np.vstack(relations)

    def lift(v):
        l = (operators @ v % p).T @ x_inv % p
        return l, (b_inv @ l % p) @ a0 % p

    return matrix, lift


def projected_equations(a, b, p):
    """Eliminate R using the stacked target's column space when it is concise."""
    k, m, n = a.shape
    b_stack = b.reshape(k * m, n)
    _, row_ids = echelon(b_stack.T, p)
    if len(row_ids) != n or rank(a.reshape(k * m, n), p) != n:
        return None
    constraint_count = (k * m - n) * n * m * m
    if constraint_count > 12_000_000:
        return None
    # H spans the left nullspace of B_stack, so ker H is exactly its column space.
    h = kernel(b_stack.T, p).reshape(-1, k, m)
    equations = np.einsum("tir,icj->tjrc", h, a, optimize=True) % p
    equations = equations.reshape((k * m - n) * n, m * m)
    b_inv = inverse(b_stack[row_ids], p)

    def lift(vector):
        l = vector.reshape(m, m)
        r = b_inv @ (l @ a % p).reshape(k * m, n)[row_ids] % p
        return l, r

    return equations, lift


def small_side(a, b, p, cap, rng):
    """Complete over small projective GL candidates when the unit searches finish."""
    k, m, n = a.shape
    transpose = m > n
    if transpose:
        a = a.transpose(0, 2, 1)
        b = b.transpose(0, 2, 1)
        m, n = n, m
    left = projective(p, m * m, 512)
    if left is None or k * m * n * n * n > 1_000_000:
        return None, False
    b_maps = [np.kron(mat, np.eye(n, dtype=np.int64)) for mat in b]
    complete = True
    for candidate in left:
        l = candidate.reshape(m, m)
        if rank(l, p) < m:
            continue
        src = (l @ a % p).reshape(k, m * n)
        complement = kernel(src, p)
        constraints = np.vstack([complement @ b_map % p for b_map in b_maps])
        w, decided = sparse_unit(kernel(constraints, p), m, n, p, cap, rng,
                                 fixed_l=l)
        complete &= decided
        if w is None:
            continue
        _, r = w
        right = (b @ r % p).reshape(k, m * n)
        _, cols = echelon(right, p)
        s = (src[:, cols] @ inverse(right[:, cols], p) % p).T
        if transpose:
            return (inverse(r.T, p), inverse(l.T, p), s), True
        return (l, r, s), True
    return None, complete


def fixed_map(a, b, s, p, rng, cap):
    k, m, n = a.shape
    images = (s.T @ b.reshape(k, m * n) % p).reshape(k, m, n)
    cyclic = cyclic_equations(a, images, p)
    if cyclic is not None:
        equations, lift = cyclic
        w, complete = sparse_unit(kernel(equations, p), m, n, p, cap, rng, lift)
        return w, complete, "cyclic"
    transposed = m > n
    projected = projected_equations(a.transpose(0, 2, 1), images.transpose(0, 2, 1), p) if transposed else projected_equations(a, images, p)
    if projected is not None:
        equations, lift = projected
        rows, cols = (n, m) if transposed else (m, n)
        w, complete = sparse_unit(kernel(equations, p), rows, cols, p, cap, rng, lift)
        if w is not None and transposed:
            l, r = w
            w = inverse(r.T, p), inverse(l.T, p)
        return w, complete, "projected"
    if k * m * n * (m * m + n * n) > 12_000_000:
        return None, False, "linear_memory_cap"
    left_eye = np.eye(m, dtype=np.int64)
    right_eye = np.eye(n, dtype=np.int64)
    blocks = [
        np.hstack((np.kron(left_eye, x.T), -np.kron(y, right_eye) % p))
        for x, y in zip(a, images)
    ]
    w, complete = sparse_unit(kernel(np.vstack(blocks), p), m, n, p, cap, rng)
    return w, complete, "linear"


def coordinates(source, target, p):
    """Rows of source as coefficients on the independent rows of target."""
    _, indices = echelon(target, p)
    return source[:, indices] @ inverse(target[:, indices], p) % p


def solve(p, a, b, projective_cap=100_000, search_cap=8192, max_anchors=96, rounds=3):
    start = perf_counter()
    k, m, n = a.shape
    stats = {}
    rng = np.random.default_rng(31333)

    def result(status, reason, witness=None):
        report = dict(status=status, reason=reason, format=(p, m, n, k), **stats,
                      total_ms=(perf_counter() - start) * 1000)
        if witness is not None:
            l, r, s = witness
            if not verify(a, b, p, l, r, s):
                raise RuntimeError("The candidate witness failed exact verification")
            report["verified_ms"] = (perf_counter() - start) * 1000
            report["witness"] = {"L": l.tolist(), "R": r.tolist(), "S": s.tolist()}
        return report

    stats['native_rank'] = bool(NATIVE_RANK_WORDS)
    def fallback(reason):
        begin = perf_counter()
        witness, decided = small_side(a, b, p, search_cap, rng)
        stats["small_side_ms"] = (perf_counter() - begin) * 1000
        if witness is not None:
            return result("yes", "small_side_exact", witness)
        return result("no" if decided else "unknown", "small_side_exhausted" if decided else reason)

    if rank(a.reshape(k, -1), p) != k or rank(b.reshape(k, -1), p) != k:
        return result("invalid", "dependent_generator_rows")
    row = lambda x: x.transpose(1, 0, 2).reshape(m, k * n)
    if rank(row(a), p) != rank(row(b), p) or rank(a.reshape(k * m, n), p) != rank(b.reshape(k * m, n), p):
        return result("no", "different_support_dimensions")
    if np.array_equal(a, b):
        return result("yes", "identical", [np.eye(d, dtype=np.int64) for d in (m, n, k)])
    ambient = m * n
    if k > ambient // 2:
        aa = kernel(a.reshape(k, ambient), p).reshape(ambient - k, m, n)
        bb = kernel(b.reshape(k, ambient), p).reshape(ambient - k, m, n)
        if len(aa):
            dual = solve(p, aa, bb, projective_cap, search_cap, max_anchors, rounds)
            stats["dual_dimension"] = len(aa)
            stats["dual_reason"] = dual["reason"]
            if dual["status"] != "yes":
                return result(dual["status"], "trace_dual")
            w = dual["witness"]
            ll = inverse(np.array(w["L"], dtype=np.int64).T, p)
            rr = inverse(np.array(w["R"], dtype=np.int64).T, p)
        else:
            ll, rr = np.eye(m, dtype=np.int64), np.eye(n, dtype=np.int64)
        s = coordinates((ll @ a % p).reshape(k, ambient),
                        (b @ rr % p).reshape(k, ambient), p).T
        return result("yes", "trace_dual", (ll, rr, s))
    points = projective(p, k, projective_cap)
    if points is None:
        return fallback("projective_cap")
    stats["points"] = len(points)
    begin = perf_counter()
    ra, rb = rank_word_table(a, points, p), rank_word_table(b, points, p)
    stats["ranks_ms"] = (perf_counter() - begin) * 1000
    an = np.bincount(ra, minlength=min(m, n) + 1)
    bn = np.bincount(rb, minlength=min(m, n) + 1)
    stats["rank_histogram"] = an.tolist()
    if not np.array_equal(an, bn):
        return result("no", "different_projective_rank_histogram")
    if min(m, n) <= 2:
        early = fallback("small_side_incomplete")
        if early["status"] != "unknown":
            return early
    use = []
    for r in sorted(np.flatnonzero(an), key=lambda j: (an[j], j)):
        if sum(an[i] for i in use) + an[r] > max_anchors:
            continue
        use.append(r)
        if sum(an[i] for i in use) >= k + 1:
            break
    ax, bx = points[np.isin(ra, use)], points[np.isin(rb, use)]
    stats["anchors"] = len(ax)
    if len(ax) < k:
        return fallback("too_few_rare_rank_directions")
    begin = perf_counter()
    ac, bc, detail = joint_point_colors(points, ax, bx, ra[np.isin(ra, use)], rb[np.isin(rb, use)], p, rounds)
    stats["colors"] = len(set(ac))
    stats["refinement_ms"] = (perf_counter() - begin) * 1000
    if detail == "incompatible":
        return result("no", "rank_incidence_color_histogram")
    begin = perf_counter()
    complete, visits, transforms = coefficient_maps(ax, bx, ac, bc, p, search_cap)
    stats["coefficient_ms"] = (perf_counter() - begin) * 1000
    stats["visited"] = visits
    stats["coefficient_candidates"] = len(transforms)
    stats["coefficient_complete"] = complete
    for s in transforms:
        witness, decided, method = fixed_map(a, b, s, p, rng, search_cap)
        complete &= decided
        if witness is not None:
            return result("yes", method, (*witness, s))
    return result("no", "exhausted_compatible_maps") if complete else fallback("bounded_search")



def main():
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("pairs", nargs="+", type=Path)
    parser.add_argument("--projective-cap", type=int, default=100_000)
    parser.add_argument("--search-cap", type=int, default=8192)
    parser.add_argument("--rounds", type=int, default=3)
    args = parser.parse_args()
    for path in args.pairs:
        begin = perf_counter()
        p, a, b = read_pair(path)
        read_ms = (perf_counter() - begin) * 1000
        result = solve(p, a, b, args.projective_cap, args.search_cap, rounds=args.rounds)
        result["case"] = path.name
        result["read_ms"] = read_ms
        result["end_to_end_ms"] = (perf_counter() - begin) * 1000
        print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
