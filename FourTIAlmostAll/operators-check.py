"""Exact binary controls for the squared partial-trace covariants."""
from collections import Counter
from itertools import combinations
from random import Random

from mixed_ratio_check import CUTS, common_kernel, inv, multiply, permute


def partial_trace(matrix, n, keep):
    """Trace over one index of an operator on two n-dimensional modes."""
    rows = [0] * n
    for i in range(n):
        for j in range(n):
            entry = 0
            for k in range(n):
                row, col = (i * n + k, j * n + k) if keep == 0 else (k * n + i, k * n + j)
                entry ^= (matrix[row] >> col) & 1
            rows[i] |= entry << j
    return rows


def collect_anchors(source, inverses, n):
    single_cut = [[] for _ in range(4)]
    all_cuts = [[] for _ in range(4)]
    expected_trace = [1 << i for i in range(n)] if n % 2 else [0] * n
    for pair in combinations(range(4), 2):
        other = tuple(i for i in range(4) if i not in pair)
        forward = permute(source, n, CUTS[0], pair + other)
        for cut, inverse in zip(CUTS, inverses):
            if cut[:2] in (pair, other):
                continue
            backward = permute(inverse, n, cut[2:] + cut[:2], other + pair)
            crossed = multiply(forward, backward)
            squared = multiply(crossed, crossed)
            for keep, mode in enumerate(pair):
                assert partial_trace(crossed, n, keep) == expected_trace
                anchor = partial_trace(squared, n, keep)
                all_cuts[mode].append(anchor)
                if cut == CUTS[0]:
                    single_cut[mode].append(anchor)
    return single_cut, all_cuts


def run(n, trials, seed):
    rng = Random(seed)
    size = n * n
    mask = (1 << size) - 1
    outcomes = Counter()
    attempts = 0
    while sum(outcomes.values()) < trials:
        bits = rng.getrandbits(size * size)
        source = [(bits >> (i * size)) & mask for i in range(size)]
        attempts += 1
        inverses = []
        for cut in CUTS:
            inverse = inv(permute(source, n, CUTS[0], cut))
            if inverse is None:
                break
            inverses.append(inverse)
        if len(inverses) != len(CUTS):
            continue
        anchor_sets = collect_anchors(source, inverses, n)
        outcomes[tuple(all(common_kernel(mode, mode) == 1 for mode in anchors)
                       for anchors in anchor_sets)] += 1
    return attempts, outcomes


if __name__ == "__main__":
    for n, trials in ((3, 40), (4, 40), (5, 40), (6, 40), (8, 30), (10, 20)):
        print(n, *run(n, trials, n * 91), flush=True)
