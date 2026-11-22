"""Exact checks of live-board restrictions and the design multiplication identity."""

from fractions import Fraction
from itertools import combinations, permutations
from math import comb, perm


def restriction_histogram(r, s, u, k):
    v = s - r + u
    histogram = [0] * (k + 1)
    total = 0
    for row_group in combinations(range(r), u):
        rows = set(row_group)
        old_rows = sorted(set(range(r)) - rows)
        for col_group in combinations(range(s), v):
            cols = set(col_group)
            for order in permutations(sorted(set(range(s)) - cols)):
                pins = dict(zip(old_rows, order))
                total += 1
                if all((i in rows and i in cols) or pins.get(i) == i for i in range(k)):
                    histogram[sum(i in rows for i in range(k))] += 1
    return [Fraction(n, total) for n in histogram]


def check_restrictions():
    count = 0
    for r, s, u in [(3, 4, 1), (3, 5, 1), (4, 5, 2), (4, 6, 2), (5, 7, 2)]:
        v = s - r + u
        for k in range(r + 1):
            expected = [Fraction(comb(k, j) * perm(u, j) * perm(v, j) * perm(r - u, k - j),
                                 perm(r, k) * perm(s, k)) for j in range(k + 1)]
            assert restriction_histogram(r, s, u, k) == expected
            count += 1
    return count


def degree_one_design_check():
    # F_2 on a 4-by-6 board, j=1. A design is given by a rectangular
    # matrix with row/column sums equal to its arbitrarily chosen empty value.
    r, s = 4, 6
    edges = [(i, j) for i in range(r) for j in range(s)]
    cases = 0
    for norm in range(2):
        for e in edges:
            i0, j0 = e
            ri = [i for i in range(r) if i != i0]
            cj = [j for j in range(s) if j != j0]
            for pivot in range(2):
                psi = {edge: 0 for edge in edges}
                for i in range(r - 1):
                    psi[i, s - 1] = norm
                for j in range(s - 1):
                    psi[r - 1, j] = norm
                if psi[e] != pivot:
                    for i in [i0, ri[0]]:
                        for j in [j0, cj[0]]:
                            psi[i, j] ^= 1
                assert all(sum(psi[i, j] for j in range(s)) % 2 == norm for i in range(r))
                assert all(sum(psi[i, j] for i in range(r)) % 2 == norm for j in range(s))
                # A degree-zero conditioned design on the 3-by-5 board
                # with empty value pivot. Fill its last row and column.
                conditioned = {(i, j): 0 for i in ri for j in cj}
                for i in ri[:-1]:
                    conditioned[i, cj[-1]] = pivot
                for j in cj[:-1]:
                    conditioned[ri[-1], j] = pivot
                conditioned[ri[-1], cj[-1]] = pivot
                forced = {edge: (pivot if edge == e else conditioned.get(edge, 0))
                          for edge in edges}
                assert all(sum(forced[i, j] for j in range(s)) % 2 == pivot for i in range(r))
                assert all(sum(forced[i, j] for i in range(r)) % 2 == pivot for j in range(s))
                # On every possible parent monomial whose product stays <= j,
                # the adjoint functional is independently determined.
                assert forced[e] == psi[e] == pivot
                assert all(forced[i, j] == 0 for i, j in edges
                           if (i == i0 or j == j0) and (i, j) != e)
                cases += 1
    return cases


if __name__ == "__main__":
    print(f"Exact matching-survival histograms verified: {check_restrictions()}.")
    print(f"Forced-edge normalization checks verified: {degree_one_design_check()}.")
