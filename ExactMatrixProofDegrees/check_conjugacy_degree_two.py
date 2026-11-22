"""Direct degree-two PC span on binary Jordan representatives through side four."""

from itertools import combinations


def partitions(n, maximum=None):
    if n == 0:
        yield ()
        return
    for first in range(1, min(n, maximum or n) + 1):
        for rest in partitions(n - first, first):
            yield (first,) + rest


def jordan(blocks):
    n = sum(map(sum, blocks))
    matrix = [[0] * n for _ in range(n)]
    start = 0
    for eigenvalue, lengths in enumerate(blocks):
        for length in lengths:
            for j in range(start, start + length):
                matrix[j][j] = eigenvalue
                if j + 1 < start + length:
                    matrix[j][j + 1] = 1
            start += length
    return matrix


def degree_two(a, b):
    n = len(a)
    variables = n * n
    basis = {}

    def insert(row):
        while row:
            pivot = row.bit_length()
            if pivot not in basis:
                basis[pivot] = row
                return
            row ^= basis[pivot]

    def xy(x, y):
        return 1 << (1 + variables * y + x)

    for i in range(n):
        for j in range(n):
            linear = 0
            for k in range(n):
                linear ^= a[k][j] << (n * i + k)
                linear ^= b[i][k] << (n * k + j)
            for y in range(variables):
                insert(linear << (1 + variables * y))
    for i in range(n):
        for j in range(n):
            forward = reverse = int(i == j)
            for k in range(n):
                forward ^= xy(n * i + k, n * k + j)
                reverse ^= xy(n * k + j, n * i + k)
            insert(forward)
            insert(reverse)
    return 1 in basis


if __name__ == "__main__":
    count = 0
    for n in range(1, 5):
        types = [(a, b) for m in range(n + 1)
                 for a in partitions(m) for b in partitions(n - m)]
        for left, right in combinations(types, 2):
            expected = any(max(a, default=0) != max(b, default=0) or
                           (sum(a) - sum(b)) % 2 for a, b in zip(left, right))
            assert degree_two(jordan(left), jordan(right)) == expected, (left, right)
            count += 1
    print(f"Verified the direct degree-two PC span for {count} binary Jordan pairs.")
