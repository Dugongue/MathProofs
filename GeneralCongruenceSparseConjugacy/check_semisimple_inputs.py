"""Enumerate all Hall rectangles directly on small labelled boards."""

from itertools import combinations, combinations_with_replacement


def min_cut(source, target):
    n = len(source)
    best = n * n + 1
    for rows_used in range(1, n + 1):
        columns_needed = n + 1 - rows_used
        if rows_used * columns_needed >= best:
            continue
        for rows in combinations(range(n), rows_used):
            labels = {target[i] for i in rows}
            if sum(label not in labels for label in source) >= columns_needed:
                best = rows_used * columns_needed
                break
    return best


if __name__ == "__main__":
    cases = 0
    for n in range(1, 8):
        types = list(combinations_with_replacement(range(3), n))
        for source, target in combinations(types, 2):
            gaps = [(source.count(i), target.count(i)) for i in range(3)]
            m = min(min(a, b) for a, b in gaps if a != b)
            assert min_cut(source, target) == (m + 1) * (n - m)
            cases += 1
    print(f"Direct Hall-rectangle minima verified on {cases} three-label multiplicity pairs.")
