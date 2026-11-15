"""Rank-anchor stage using CaDiCaL, followed by exact coefficient-map lifting."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import tempfile
from time import perf_counter

import numpy as np

from ref_cadical import Circuit, ConstructionLimit
from ref_hull import inverse, kernel, rref, space_rank, vectors
from ref_io import read_pair, verify


def projective(p, k):
    parts = []
    for first in range(k):
        dims = k - first - 1
        numbers = np.arange(p ** dims, dtype=np.int64)
        points = np.zeros((len(numbers), k), dtype=np.int64)
        points[:, first] = 1
        for axis in range(first + 1, k):
            points[:, axis] = numbers % p
            numbers //= p
        parts.append(points)
    return np.concatenate(parts)


def rank_batch(matrices, p):
    matrices = matrices.copy()
    t, m, n = matrices.shape
    rr = np.arange(m)
    fields_inverse = np.array([0] + [pow(i, -1, p) for i in range(1, p)],
                              dtype=np.int64)
    rank = np.zeros(t, dtype=np.int64)
    for col in range(n):
        good = (matrices[:, :, col] != 0) & (rr[None, :] >= rank[:, None])
        active = np.flatnonzero(np.any(good, axis=1))
        if len(active) == 0:
            continue
        cand = np.argmax(good[active], axis=1)
        piv = rank[active]
        old = matrices[active, piv].copy()
        matrices[active, piv] = matrices[active, cand]
        matrices[active, cand] = old
        leading = matrices[active, piv, col:]
        leading = leading * fields_inverse[leading[:, 0]][:, None] % p
        factors = matrices[active, :, col] * (rr[None, :] > piv[:, None])
        matrices[active, :, col:] = (
            matrices[active, :, col:] - factors[:, :, None] * leading[:, None, :]
        ) % p
        rank[active] += 1
    return rank


def ranks(points, code, p):
    k, m, n = code.shape
    flattened = code.reshape(k, -1)
    return np.concatenate([
        rank_batch(((points[j:j+4096] @ flattened) % p).reshape(-1, m, n), p)
        for j in range(0, len(points), 4096)
    ])


def constrain_membership(c, vector, targets, p, one_chart=False):
    selectors = []
    anchors = []
    for point in targets:
        group = []
        choose_anchor = c.var()
        anchors.append(choose_anchor)
        scalars = (1,) if one_chart else range(1, p)
        for scale in scalars:
            vec = point * scale % p
            choose = c.var()
            group.append(choose)
            c.clause(-choose, choose_anchor)
            for symbol, value in zip(vector, vec):
                for bit, rhs in zip(symbol, c.constant(int(value))):
                    c.clause(-choose, bit if rhs == c.true else -bit)
        c.clause(-choose_anchor, *group)
        selectors.extend(group)
    c.clause(*selectors)
    return anchors


def construct(c, left, coordinates, target_points, p):
    k = len(left)
    row_images = c.matrix(k, k)
    anchor_images = []
    for u in coordinates:
        relevant = np.flatnonzero(u)
        is_first = len(relevant) == 1 and int(relevant[0]) == 0
        image = [c.dot((c.constant(int(u[i])), row_images[i][j]) for i in relevant)
                 for j in range(k)]
        anchor_images.append(constrain_membership(c, image, target_points, p, is_first))
    # An invertible linear map acts injectively on projective points.
    for images in zip(*anchor_images):
        for a, b in itertools.combinations(images, 2):
            c.clause(-a, -b)
    return row_images


def lift(a, b, s, p, rng):
    k, m, n = a.shape
    moved_b = (s @ b.reshape(k, -1) % p).reshape(k, m, n)
    left = np.eye(m, dtype=np.int64)
    right = np.eye(n, dtype=np.int64)
    linear = np.vstack([
        np.concatenate([np.kron(left, x.T), -np.kron(y, right)], axis=1)
        for x, y in zip(a, moved_b)
    ])
    space = kernel(linear, p)
    for candidate in vectors(space, p, rng, 64):
        l = candidate[:m*m].reshape(m, m)
        r_inv = candidate[m*m:].reshape(n, n)
        if space_rank(l, p) == m and space_rank(r_inv, p) == n:
            return (l, inverse(r_inv, p)), True
    if p ** len(space) <= 10000:
        for coeff in itertools.product(range(p), repeat=len(space)):
            candidate = np.array(coeff, dtype=np.int64) @ space % p
            l = candidate[:m*m].reshape(m, m)
            r_inv = candidate[m*m:].reshape(n, n)
            if space_rank(l, p) == m and space_rank(r_inv, p) == n:
                return (l, inverse(r_inv, p)), True
        return None, True
    return None, False


def solve(path, cadical, timeout, limit, max_points, max_models):
    start = perf_counter()
    p, m, n, k, a_raw, b_raw = read_pair(path)
    after_read = perf_counter()
    result = {"case": path.name, "format": [p, m, n, k], "backend": "CaDiCaL rank-anchor",
              "read_ms": 1000 * (after_read - start)}
    if p > 65521 or (p ** k - 1) // (p - 1) > max_points:
        return result | {"result": "unknown", "reason": "projective point cap"}
    a, b = np.array(a_raw, dtype=np.int64), np.array(b_raw, dtype=np.int64)
    if space_rank(a.reshape(k, -1), p) != k or space_rank(b.reshape(k, -1), p) != k:
        return result | {"result": "unknown", "reason": "requires independent input bases"}
    points = projective(p, k)
    a_ranks, b_ranks = ranks(points, a, p), ranks(points, b, p)
    a_counts = np.bincount(a_ranks, minlength=min(m, n) + 1)
    b_counts = np.bincount(b_ranks, minlength=min(m, n) + 1)
    if not np.array_equal(a_counts, b_counts):
        elapsed = perf_counter()
        return result | {"result": "no", "reason": "rank distributions differ",
                         "profile_ms": 1000 * (elapsed - after_read),
                         "total_ms": 1000 * (elapsed - start)}
    colour = int(np.flatnonzero(a_counts)[0])
    a_pts, b_pts = points[a_ranks == colour], points[b_ranks == colour]
    _, basis_indices = rref(a_pts.T, p)
    after_ranks = perf_counter()
    result.update(points=len(points), anchor_count=len(a_pts),
                  profile_ms=1000 * (after_ranks - after_read))
    if len(basis_indices) != k:
        return result | {"result": "unknown", "reason": "minimum-rank anchors do not span",
                         "total_ms": 1000 * (perf_counter() - start)}
    basis = a_pts[basis_indices]
    coordinates = a_pts @ inverse(basis, p) % p
    result["result"] = "unknown"
    unknown_lift = False
    rng = np.random.default_rng(1)
    with tempfile.TemporaryDirectory(prefix="mce-anchors-") as temporary:
        body = Path(temporary) / "anchor.cnf"
        with body.open("w+", encoding="ascii", newline="\n") as f:
            f.write(" " * 96 + "\n")
            circuit = Circuit(f, p, limit)
            try:
                row_images = construct(circuit, basis, coordinates, b_pts, p)
            except ConstructionLimit:
                return result | {"result": "unknown", "reason": "clause cap",
                                 "total_ms": 1000 * (perf_counter() - start)}
            f.seek(0)
            header = f"p cnf {circuit.variables} {circuit.clauses}"
            f.write(header + " " * (96 - len(header)))
        result["build_ms"] = 1000 * (perf_counter() - after_ranks)
        result["clauses"] = circuit.clauses
        models = 0
        sat_ms = 0.
        lift_ms = 0.
        for _ in range(max_models):
            remaining = timeout - (perf_counter() - start)
            if remaining <= 0:
                result["reason"] = "time budget"
                break
            sat_start = perf_counter()
            try:
                process = subprocess.run([str(cadical), "-q", str(body)],
                                         capture_output=True, text=True, timeout=remaining)
            except subprocess.TimeoutExpired:
                sat_ms += 1000 * (perf_counter() - sat_start)
                result["reason"] = "SAT timeout"
                break
            sat_ms += 1000 * (perf_counter() - sat_start)
            if process.returncode == 20:
                result["result"] = "unknown" if unknown_lift else "no"
                result["reason"] = "remaining anchors unsatisfiable"
                break
            if process.returncode != 10:
                result["reason"] = f"unexpected SAT exit {process.returncode}"
                break
            models += 1
            true = {int(x) for line in process.stdout.splitlines() if line.startswith("v ")
                    for x in line.split()[1:]}
            t = np.array([[sum(1 << z for z, lit in enumerate(bits) if lit in true)
                           for bits in row] for row in row_images], dtype=np.int64)
            s = inverse(basis, p) @ t % p
            if space_rank(s, p) == k:
                begin_lift = perf_counter()
                found, certain = lift(a, b, s, p, rng)
                lift_ms += 1000 * (perf_counter() - begin_lift)
                if found:
                    l, r = found
                    witness = l.tolist(), r.tolist(), s.tolist()
                    begin_check = perf_counter()
                    if not verify(p, m, n, k, a_raw, b_raw, *witness):
                        raise AssertionError("Rank-anchor SAT witness failed verification")
                    result.update(result="yes", verify_ms=1000 * (perf_counter() - begin_check))
                    result.update(zip(("left", "right", "mixing"), witness))
                    break
                unknown_lift |= not certain
            opposite = [-lit if lit in true else lit for row in row_images
                        for bits in row for lit in bits]
            circuit.clauses += 1
            with body.open("r+", encoding="ascii", newline="\n") as f:
                header = f"p cnf {circuit.variables} {circuit.clauses}"
                f.write(header + " " * (96 - len(header)))
                f.seek(0, 2)
                f.write(" ".join(map(str, opposite)) + " 0\n")
        result.setdefault("reason", "model budget" if result["result"] == "unknown" else None)
        result.update(sat_ms=sat_ms, lift_ms=lift_ms, models=models)
    result["total_ms"] = 1000 * (perf_counter() - start)
    return result


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("cases", nargs="+", type=Path)
    cli.add_argument("--cadical", type=Path, required=True)
    cli.add_argument("--timeout", type=float, default=5)
    cli.add_argument("--clause-limit", type=int, default=2_000_000)
    cli.add_argument("--max-points", type=int, default=200000)
    cli.add_argument("--max-models", type=int, default=100)
    args = cli.parse_args()
    for path in args.cases:
        print(json.dumps(solve(path, args.cadical.resolve(), args.timeout,
                               args.clause_limit, args.max_points, args.max_models)), flush=True)
