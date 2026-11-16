"""Exact binary controls for mixed flattening ratios in ordinary 4-tensor isomorphism."""
import argparse
from collections import Counter
from random import Random


CUTS = ((0, 1, 2, 3), (0, 2, 1, 3), (0, 3, 1, 2))


def permute(tensor, n, src, dst):
    """Interpret rows and columns as an ordered list of four base-n axes."""
    out = [0] * (n * n)
    actions = [src.index(i) for i in dst]
    for row, bits in enumerate(tensor):
        while bits:
            q = bits & -bits
            col = q.bit_length() - 1
            bits ^= q
            vals = row // n, row % n, col // n, col % n
            a, b, c, d = (vals[i] for i in actions)
            out[a * n + b] |= 1 << (c * n + d)
    return out


def inv(rows):
    size = len(rows)
    m = [r | (1 << (size + i)) for i, r in enumerate(rows)]
    for j in range(size):
        pivot = next((i for i in range(j, size) if (m[i] >> j) & 1), None)
        if pivot is None:
            return None
        m[j], m[pivot] = m[pivot], m[j]
        for i in range(size):
            if i != j and (m[i] >> j) & 1:
                m[i] ^= m[j]
    return [r >> size for r in m]


def multiply(A, B):
    out = []
    for row in A:
        r = 0
        while row:
            q = row & -row
            row ^= q
            r ^= B[q.bit_length() - 1]
        out.append(r)
    return out


def common_kernel(A, B):
    """Nullity of the equations X A_h = B_h X."""
    size = len(A[0])
    pivots = [0] * (size * size)
    rank = 0
    for a, b in zip(A, B):
        acols = [0] * size
        for i, bits in enumerate(a):
            while bits:
                q = bits & -bits
                bits ^= q
                acols[q.bit_length() - 1] |= 1 << i
        for i, row in enumerate(b):
            for j, col in enumerate(acols):
                v = (col << (i * size)) ^ (sum(1 << (k * size) for k in range(size) if row >> k & 1) << j)
                while v:
                    k = v.bit_length() - 1
                    if pivots[k]:
                        v ^= pivots[k]
                    else:
                        pivots[k] = v
                        rank += 1
                        break
    return size * size - rank


def ratios(flattenings, inverses, n, base=0):
    left = CUTS[base][:2]
    right = CUTS[base][2:]
    return [
        multiply(flattenings[base], permute(inverses[q], n, CUTS[q][2:] + CUTS[q][:2], right + left))
        for q in range(3) if q != base
    ]


def random_invertible(size, rng):
    while True:
        rows = [rng.getrandbits(size) for _ in range(size)]
        if inv(rows) is not None:
            return rows


def tensor_product(a, b):
    size = len(a)
    return [
        sum(b[j] << (k * size) for k in range(size) if a[i] >> k & 1)
        for i in range(size) for j in range(size)
    ]


def transpose(matrix):
    size = len(matrix)
    return [sum(((row >> j) & 1) << i for i, row in enumerate(matrix))
            for j in range(size)]


def check_relabeling(source, source_ratios, n, rng):
    modes = [random_invertible(n, rng) for _ in range(4)]
    p, q = tensor_product(*modes[:2]), tensor_product(*modes[2:])
    target = multiply(multiply(p, source), transpose(q))
    target_flat = [target] + [permute(target, n, CUTS[0], cut) for cut in CUTS[1:]]
    target_inverse = [inv(flat) for flat in target_flat]
    assert all(flat is not None for flat in target_inverse)
    target_ratios = ratios(target_flat, target_inverse, n)
    for a, b in zip(source_ratios, target_ratios):
        assert multiply(p, a) == multiply(b, p)
    assert common_kernel(source_ratios, target_ratios) == common_kernel(
        source_ratios, source_ratios
    )


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--samples", type=int, default=50)
    ap.add_argument("--min-n", type=int, default=3)
    ap.add_argument("--max-n", type=int, default=5)
    ap.add_argument("--seed", type=int, default=514)
    ap.add_argument("--max-attempts", type=int, default=100000)
    ap.add_argument("--check-relabeling", action="store_true")
    args = ap.parse_args()
    if not 3 <= args.min_n <= args.max_n or args.samples < 1 or args.max_attempts < 1:
        ap.error("Require 3 <= min-n <= max-n and positive sample and attempt counts.")
    rng = Random(args.seed)
    relabel_rng = Random(args.seed)
    for n in range(args.min_n, args.max_n + 1):
        histogram = Counter()
        attempts = 0
        while sum(histogram.values()) < args.samples:
            if attempts >= args.max_attempts:
                raise RuntimeError(f"Attempt limit reached for n={n}: {histogram}")
            x = [rng.getrandbits(n * n) for _ in range(n * n)]
            attempts += 1
            ax = inv(x)
            if ax is None:
                continue
            y, z = [permute(x, n, CUTS[0], t) for t in CUTS[1:]]
            ay, az = inv(y), inv(z)
            if ay is None or az is None:
                continue
            flat, inverse = [x, y, z], [ax, ay, az]
            a = ratios(flat, inverse, n)
            if args.check_relabeling:
                check_relabeling(x, a, n, relabel_rng)
            first = common_kernel(a, a)
            opt = first
            if first > 1:
                for base in (1, 2):
                    a = ratios(flat, inverse, n, base)
                    opt = min(opt, common_kernel(a, a))
                    if opt == 1:
                        break
            histogram[first, opt] += 1
        print(n, attempts, sorted(histogram.items()), flush=True)


if __name__ == "__main__":
    main()
