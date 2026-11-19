"""Cross-check the common divisor criterion against the full Weyr inequalities.
Run with Python 3. No external packages. Each of two eigenvalues has a partition,
and a third unoccupied eigenvalue allows specialization away from both.
"""

from itertools import product


def partitions(total, maximum=None):
    if total == 0:
        yield ()
        return
    if maximum is None:
        maximum = total
    for head in range(1, min(total, maximum) + 1):
        for tail in partitions(total - head, head):
            yield (head,) + tail


def weyr(prefixes, block_size, defect, allocation):
    for blocks, count in zip(prefixes, allocation):
        for j in range(1, max((count,) + blocks) + 1):
            if block_size * min(j, count) > defect * j + sum(min(j, d) for d in blocks):
                return False
    return True


def divisor_capacity(blocks, a, b, rank):
    size = a * b
    padded = tuple(sorted(blocks + (0,) * (rank - len(blocks))))
    return min([a] + [
        sum(padded[:size-b+s]) // s for s in range(1, b+1) if size-b+s <= rank
    ])


if __name__ == "__main__":
    cases = 0
    for a, b in product(range(1, 4), repeat=2):
        size = a * b
        allocations = [(i, j, a-i-j) for i in range(a+1) for j in range(a-i+1)]
        for rank in range(size+1):
            for i in range(rank+1):
                for j in range(rank-i+1):
                    for first, second in product(partitions(i), partitions(j)):
                        blocks = (first, second, ())
                        via_weyr = any(weyr(blocks, b, size-rank, t) for t in allocations)
                        via_divisors = sum(divisor_capacity(B, a, b, rank) for B in blocks) >= a
                        assert via_weyr == via_divisors, (a, b, rank, blocks)
                        cases += 1
    assert divisor_capacity((4,), 2, 2, 4) == 0
    assert divisor_capacity((2, 2), 2, 2, 4) == 2
    print("Matched Weyr and divisor tests in", cases, "configurations.")
