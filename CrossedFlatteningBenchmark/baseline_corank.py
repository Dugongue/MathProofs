"""GF(2) implementation of the corank-three algorithm in arXiv:2604.00591 §4."""

import argparse
from itertools import product
import json
from pathlib import Path
from time import perf_counter

from baseline_external import eliminate, parse_pair, verify_witness


def transpose(a):
    return [list(column) for column in zip(*a)]


def matrix_product(a, b):
    return [[sum(x*y for x, y in zip(row, col)) & 1 for col in zip(*b)]
            for row in a]


def dense(words, n):
    return [[word >> (i*n+j) & 1 for j in range(n)] for i, word in enumerate(words)]


def bitmask(row):
    return sum(x << i for i, x in enumerate(row))


def nullspace(equations, width):
    pivots = {}
    for row in equations:
        row = bitmask(row) if not isinstance(row, int) else row
        while row:
            pivot = row.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = row
                break
            row ^= pivots[pivot]
    basis = []
    for i in range(width):
        if i in pivots:
            continue
        v = 1 << i
        for j in sorted(pivots):
            if (pivots[j] & v).bit_count() & 1:
                v |= 1 << j
        basis.append(v)
    return basis


def codewords(basis):
    values = [0]
    for basis_word in basis:
        values.extend([x ^ basis_word for x in values])
    return values


def invertible_words(values, n):
    for value in values:
        mat = dense([value] * n, n)
        inverse = eliminate(mat, 2, augmented=True)
        if inverse is not None:
            yield value, mat, inverse


def intertwiners(source, target, n):
    equations = []
    for x, y in zip(source, target):
        for i, j in product(range(n), repeat=2):
            a, b = 0, 0
            for k in range(n):
                a |= y[i][k] << (k*n+j)
                b |= x[k][j] << (i*n+k)
            equations.append(a ^ b)
    return nullspace(equations, n*n)


def normalized_source(code, n):
    vals = codewords(code)
    first = next(invertible_words(vals, n), None)
    if first is None:
        return None, "source kernel code contains no invertible matrix"
    a, mat, inverse = first
    b = next(x for x in vals if x not in (0, a))
    c = next(x for x in vals if x not in (0, a, b, a ^ b))
    ratios = [matrix_product(inverse, dense([x] * n, n)) for x in (b, c)]
    stabilizer_space = intertwiners(ratios, ratios, n)
    if len(stabilizer_space) > 14:
        return None, "benchmark cap on centralizer-space enumeration"
    count = 0
    for _ in invertible_words(codewords(stabilizer_space), n):
        count += 1
        if count > 2:
            return None, "source stabilizer exceeds published cutoff"
    return (mat, ratios, len(stabilizer_space)), None


def compare_kernel(normalized, target_code, n, deadline):
    first, source_ratios, centralizer_dim = normalized
    vals = codewords(target_code)
    candidates = []
    for a, _, inverse in invertible_words(vals, n):
        others = {x: matrix_product(inverse, dense([x] * n, n))
                  for x in vals if x not in (0, a)}
        for b in others:
            for c in others:
                if c in (b, a ^ b):
                    continue
                if perf_counter() >= deadline:
                    return None
                linear = intertwiners(source_ratios, (others[b], others[c]), n)
                if len(linear) != centralizer_dim:
                    continue  # An invertible intertwiner forces this dimension.
                for _, r, r_inv in invertible_words(codewords(linear), n):
                    l_t = matrix_product(matrix_product(first, r_inv), inverse)
                    candidates.append((transpose(l_t), r))
    return candidates


def permute(data, n, axes):
    out = []
    for q in product(range(n), repeat=4):
        old = [0] * 4
        for i, j in enumerate(axes):
            old[j] = q[i]
        a,b,c,d = old
        out.append(((a*n+b)*n+c)*n+d)
    return [data[index] for index in out]


def kernel_codes(data, n):
    size = n*n
    flattening = [data[i:i+size] for i in range(0, len(data), size)]
    return nullspace(transpose(flattening), size), nullspace(flattening, size)


def cut_solver(source, target, n, deadline):
    ls, rs = kernel_codes(source, n)
    lt, rt = kernel_codes(target, n)
    if len(ls) != len(lt):
        return {"status": "no", "reason": "different flattening ranks"}
    if len(ls) != 3:
        return {"status": "unknown", "reason": f"flattening corank {len(ls)}"}
    initial_a, reason_a = normalized_source(ls, n)
    if reason_a:
        return {"status": "unknown", "reason": reason_a}
    initial_b, reason_b = normalized_source(rs, n)
    if reason_b:
        return {"status": "unknown", "reason": reason_b}
    first = compare_kernel(initial_a, lt, n, deadline)
    if first is None:
        return {"status": "unknown", "reason": "kernel-matching timeout"}
    second = compare_kernel(initial_b, rt, n, deadline)
    if second is None:
        return {"status": "unknown", "reason": "kernel-matching timeout"}
    for a, b in first:
        for c, d in second:
            if perf_counter() >= deadline:
                return {"status": "unknown", "reason": "witness-check timeout"}
            w = [a,b,c,d]
            if verify_witness(2, (n,)*4, source, target, w):
                return {"status": "yes", "witness": w, "kernel_candidates": [len(first), len(second)]}
    return {"status": "no", "kernel_candidates": [len(first), len(second)]}


def solve_file(path, timeout, all_cuts=False):
    start = perf_counter()
    instance = json.loads(Path(path).read_text(encoding="utf-8-sig"))
    field, dims, src, dst = parse_pair(instance)
    read_s = perf_counter() - start
    result = {"status": "unknown", "reason": "implementation requires equal sides over GF(2)"}
    if field == 2 and len(dims) == 4 and len(set(dims)) == 1:
        axes_list = [(0,1,2,3), (0,2,1,3), (0,3,1,2)] if all_cuts else [(0,1,2,3)]
        declines = []
        for axes in axes_list:
            source = permute(src, dims[0], axes)
            target = permute(dst, dims[0], axes)
            result = cut_solver(source, target, dims[0], start+timeout)
            result["axes"] = axes
            if result["status"] == "yes":
                w = [result["witness"][axes.index(i)] for i in range(4)]
                check = perf_counter()
                assert verify_witness(field, dims, src, dst, w)
                result.update(witness=w, verify_seconds=perf_counter()-check)
            if result["status"] != "unknown":
                break
            declines.append(result["reason"])
            if perf_counter() >= start+timeout:
                break
        if declines:
            result["declines"] = declines
    return dict(result, solver="corank-three", field=field, dims=dims,
                id=instance.get("id", Path(path).stem), read_seconds=read_s,
                elapsed_seconds=perf_counter()-start)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--all-cuts", action="store_true")
    parser.add_argument("pairs", nargs="+", type=Path)
    args = parser.parse_args()
    for pair in args.pairs:
        print(json.dumps(solve_file(pair, args.timeout, args.all_cuts)), flush=True)


if __name__ == "__main__":
    main()
