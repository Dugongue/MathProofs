"""Check the dense integral idempotents and minimal forward-input support."""

from itertools import product


def integral_example(r, g):
    h = r + g
    n = h + r
    return [[((int(i == j) - r) if j < h else 1) if i < h else
             ((1 - h * r) if j < h else h) for j in range(n)] for i in range(n)]


def check_examples():
    count = 0
    for r, g, prime in product(range(1, 8), range(1, 5), (2, 3, 5, 7)):
        a = integral_example(r, g)
        n = len(a)
        assert sum(a[i][i] for i in range(n)) == r + g
        for i, row in enumerate(a):
            for j in range(n):
                assert sum(x * a[k][j] for k, x in enumerate(row)) == a[i][j]
        for j in range(n):
            assert sum(i != j and bool(a[i][j] % prime) for i in range(n)) >= r - 1
        count += 1
    return count


def invertible_binary(rows):
    pivots = {}
    for row in rows:
        while row:
            column = row.bit_length()
            if column not in pivots:
                pivots[column] = row
                break
            row ^= pivots[column]
        if not row:
            return False
    return True


def forward_support_minimum(r, g):
    h = r + g
    n = r + h
    # In diagonal coordinates the only relevant equations force entries at
    # unequal eigenvalues to vanish. Count all those positions separately.
    crossing = [(i, j) for i in range(n) for j in range(n) if (i < r) != (j < h)]
    feasible = bytearray(1 << len(crossing))
    for rows in product(range(1 << n), repeat=n):
        if invertible_binary(rows):
            mask = sum(1 << t for t, (i, j) in enumerate(crossing) if rows[i] >> j & 1 == 0)
            feasible[mask] = 1
    for mask in reversed(range(len(feasible))):
        if feasible[mask]:
            bits = mask
            while bits:
                bit = bits & -bits
                feasible[mask ^ bit] = 1
                bits ^= bit
    return min(mask.bit_count() for mask, yes in enumerate(feasible) if not yes)


if __name__ == "__main__":
    print(f"Integral idempotence and modular support checks: {check_examples()}.")
    for r, g in ((1, 1), (1, 2)):
        answer = forward_support_minimum(r, g)
        assert answer == (r + g) * (r + 1)
        print(f"Exact binary forward-input minimum for r={r}, gap={g}: {answer}.")
