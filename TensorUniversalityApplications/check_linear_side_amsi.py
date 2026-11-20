from itertools import combinations, permutations, product
from random import Random


def unit(dimension, index):
    return tuple(int(i == index) for i in range(dimension))


def rank(columns, prime):
    pivots = {}
    for column in columns:
        column = [entry % prime for entry in column]
        for position in range(len(column)):
            entry = column[position]
            if not entry:
                continue
            if position not in pivots:
                inverse = pow(entry, -1, prime)
                pivots[position] = [value * inverse % prime for value in column]
                break
            column = [(x - entry * y) % prime for x, y in zip(column, pivots[position])]
    return len(pivots)


def frame_records(k):
    vectors = [unit(k, i) for i in range(k)]
    if k == 1:
        return [(vectors[0],)], set()
    if k <= 6:
        records = [(vector,) for i, vector in enumerate(vectors, 1) for _ in range(i)]
        return records + [((1,) * k,)] * (k + 1), set()
    edges = {(0, 1), (0, 2), (2, 3), (0, 4)} | {(i, i + 1) for i in range(4, k - 1)}
    records = [(vector,) for vector in vectors] + [((1,) * k,)] * 2
    return records + [(vectors[i], vectors[j]) for i, j in sorted(edges)], edges


def contains(spanning, vectors, prime):
    return rank((*spanning, *vectors), prime) == rank(spanning, prime)


def check_frames():
    checks = 0
    for prime in (2, 3, 5):
        for k in range(1, 9):
            frame = [unit(k, i) for i in range(k)]
            records, edges = frame_records(k)
            lines = {record[0] for record in records if rank(record, prime) == 1}
            assert len(lines) == k + int(k > 1)
            assert len(records) <= 5 * k
            dimensions = [sum(contains((line,), record, prime) for record in records) for line in frame]
            if k <= 6:
                assert dimensions == list(range(1, k + 1))
            else:
                assert dimensions == [1] * k
                for i, j in combinations(range(k), 2):
                    dimension = sum(contains((frame[i], frame[j]), record, prime) for record in records)
                    assert dimension == 2 + ((i, j) in edges)
                    checks += 1
            if k > 1:
                assert sum(contains(((1,) * k,), record, prime) for record in records) == (k + 1 if k <= 6 else 2)
            for j in range(len(records)):
                for ell in range(j, len(records)):
                    contraction_generators = set(records[j] + records[ell])
                    assert all(contains((line,), contraction_generators, prime) == (
                        contains((line,), records[j], prime) and contains((line,), records[ell], prime)
                    ) for line in lines)
                    checks += 1
    for k in (7, 8):
        _, edges = frame_records(k)
        identity = tuple(range(k))
        automorphisms = [
            perm for perm in permutations(range(k))
            if {tuple(sorted((perm[i], perm[j]))) for i, j in edges} == edges
        ]
        assert automorphisms == [identity]
        checks += 1
    return checks


def add_wedge(columns, left, right, coefficient):
    columns[right][left] += coefficient
    columns[left][right] -= coefficient


def check_markers():
    generator = Random(431927)
    checks = 0
    for prime, n, k in ((2, 1, 1), (2, 4, 2), (3, 4, 2), (5, 5, 3)):
        records, _ = frame_records(k)
        t = len(records)
        b = n + t
        dimension = 8 * b + 6
        for support_cutoff in (k, min(n, k + 1), n):
            support_indices = [*range(support_cutoff), *range(n, b)]
            support = [unit(dimension, i) for i in support_indices]
            old_v = [unit(dimension, i) for i in range(support_cutoff)]
            old_w = [unit(dimension, i) for i in range(n, b)]
            for coefficients in product(range(prime), repeat=2):
                first, second = coefficients
                matrix = [[0] * dimension for _ in range(dimension)]
                data = [[0] * n for _ in range(n)]
                for i, j in combinations(range(support_cutoff), 2):
                    coefficient = generator.randrange(prime)
                    add_wedge(matrix, i, j, coefficient)
                    add_wedge(data, i, j, coefficient)
                for column, record in enumerate(records):
                    for vector in record:
                        coefficient = generator.randrange(prime)
                        for i, entry in enumerate(vector):
                            if entry:
                                add_wedge(matrix, i, n + column, coefficient * entry)
                for i in range(n):
                    add_wedge(matrix, i, b + i, first)
                for i in range(n, b):
                    add_wedge(matrix, i, b + i, second)
                for i in range(2 * b, 4 * b + 2, 2):
                    add_wedge(matrix, i, i + 1, first)
                for i in range(4 * b + 2, dimension, 2):
                    add_wedge(matrix, i, i + 1, second)
                observed_rank = rank(matrix, prime)
                minimum = 2 * (b + 1) * (int(bool(first)) + 2 * bool(second))
                assert minimum <= observed_rank <= minimum + 2 * b
                checks += 1
                if first and not second:
                    assert observed_rank + len(support) - rank([*matrix, *support], prime) == support_cutoff
                    assert contains(matrix, old_v, prime)
                    checks += 1
                if second and not first:
                    assert observed_rank + len(support) - rank([*matrix, *support], prime) == t + rank(data, prime)
                    assert contains(matrix, old_w, prime)
                    checks += 1
    return checks


if __name__ == '__main__':
    frames = check_frames()
    markers = check_markers()
    print(f'PASS: {frames} frame checks and {markers} rank/intersection checks over prime fields.')
