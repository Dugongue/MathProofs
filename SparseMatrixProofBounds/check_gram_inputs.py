"""Exact Gram-input minima by binary orbit enumeration and subset search."""

from itertools import combinations


def binary_rank(rows):
    pivots = {}
    for row in rows:
        while row:
            pos = row.bit_length()
            if pos not in pivots:
                pivots[pos] = row
                break
            row ^= pivots[pos]
    return len(pivots)


def check_side(n, alternating):
    positions = [(i, j) for i in range(n) for j in range(i + int(alternating), n)]
    width = len(positions)
    size = 1 << width
    nullmask = size - 1
    orbit = {}
    for mask in range(size):
        rows = [0] * n
        diag = False
        for k, (i, j) in enumerate(positions):
            if mask >> k & 1:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
                diag |= i == j
        if not alternating and mask and not diag:
            continue
        rank = binary_rank(rows)
        orbit.setdefault(rank, []).append(mask)
    cases = 0
    for r, s in combinations(range(n // 2 + 1 if alternating else n + 1), 2):
        target = sum(1 << i for i, (a, b) in enumerate(positions)
                     if (a == b and a < s) or
                     (alternating and a % 2 == 0 and b == a + 1 and b < 2*s))
        feasible = bytearray(size)
        for gram in orbit[2*r if alternating else r]:
            feasible[nullmask ^ (target ^ gram)] = 1
        for i in range(width):
            bit = 1 << i
            for mask in range(size):
                if mask & bit and feasible[mask]:
                    feasible[mask ^ bit] = 1
        minimum = min(mask.bit_count() for mask in range(size) if not feasible[mask])
        expected = (r+1)**2 if alternating else (r+1)*(r+2)//2
        assert minimum == expected, (n, r, s, minimum, expected)
        cases += 1
    return cases


if __name__ == "__main__":
    checks = sum(check_side(n, False) for n in range(1, 6))
    checks += sum(check_side(n, True) for n in range(2, 7))
    print(f"Verified {checks} exact binary orbit input minima, including alternating side six.")
