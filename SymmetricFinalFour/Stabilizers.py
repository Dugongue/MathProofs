"""Check tangent equations for the marker-flag recovery over dual numbers."""
from itertools import combinations_with_replacement


def eliminate(row, pivots, prime, insert):
    row = {j: a % prime for j, a in row.items() if a % prime}
    while row:
        j = min(row)
        value = row[j]
        pivot = pivots.get(j)
        if pivot is None:
            if insert:
                inverse = pow(value, -1, prime)
                pivots[j] = {i: a * inverse % prime for i, a in row.items()}
            return False
        for i, a in pivot.items():
            update = (row.get(i, 0) - value * a) % prime
            if update:
                row[i] = update
            elif i in row:
                del row[i]
    return True


def tangent_system(prime, data):
    block_size = 6
    marker_start = 3 * block_size
    n = marker_start + 3
    module = {
        (i * block_size + left, i * block_size + right, marker_start + i): 1
        for i in range(3)
        for left, right in [(0, 1), (2, 3), (4, 5)]
    }
    module[0, block_size, 2 * block_size] = data
    pivots = {}
    for indices in combinations_with_replacement(range(n), 3):
        row = {}
        for slot, column in enumerate(indices):
            for r in range(n):
                replacement = list(indices)
                replacement[slot] = r
                a = module.get(tuple(sorted(replacement)), 0)
                if a:
                    j = r * n + column
                    row[j] = row.get(j, 0) + a
        row[n * n] = -module.get(indices, 0)
        eliminate(row, pivots, prime, insert=True)

    forbidden = [
        r * n + c
        for r in range(marker_start, n)
        for c in range(n)
        if c < marker_start or c != r
    ]
    for j in forbidden:
        assert eliminate({j: 1}, pivots, prime, insert=False)

    # The scalar-weight section acts dually on each affected input pair.
    weights = (1, -1, 0)
    section = {}
    for role, weight in enumerate(weights):
        x = role * block_size
        section[x * n + x] = weight
        section[(x + 1) * n + (x + 1)] = -weight
    assert all(sum(a * section.get(j, 0) for j, a in row.items()) % prime == 0
               for row in pivots.values())
    return len(pivots), len(forbidden)


def main():
    for prime in (2, 3, 5):
        for data in (0, 1):
            rank, checks = tangent_system(prime, data)
            print(f"p={prime}, input={data}: tangent constraint rank {rank}, "
                  f"{checks} marker entries forced zero and diagonal section verified")


if __name__ == "__main__":
    main()
