"""Exact falsification checks for the cyclic four-point packing and isotropy formulas."""
from functools import lru_cache
from itertools import combinations, product
from math import gcd


def all_tilings(n, tile, target=None):
    translates = [
        sum(1 << ((center + offset) % n) for offset in tile)
        for center in range(n)
    ]
    by_point = [
        [center for center, covered in enumerate(translates) if covered & (1 << point)]
        for point in range(n)
    ]

    def complete(remaining, centers):
        if not remaining:
            yield frozenset(centers)
            return
        point = (remaining & -remaining).bit_length() - 1
        for center in by_point[point]:
            covered = translates[center]
            if covered & remaining == covered:
                yield from complete(remaining ^ covered, centers + [center])

    yield from complete((1 << n) - 1 if target is None else target, [])


def predicted_tilings(n, a, b):
    if n % 4 or (a - b) % 2 == 0:
        return set()
    even_step = a if a % 2 == 0 else b
    h = gcd(n, even_step)
    if n % (2 * h):
        return set()
    expected = set()
    for parity in (0, 1):
        residues = range(parity, h, 2)
        for high in product((False, True), repeat=h // 2):
            chosen = {r + h * use_high for r, use_high in zip(residues, high)}
            expected.add(frozenset(x for x in range(n) if x % (2 * h) in chosen))
    return expected


def rref_matrices(n, k, p):
    for pivots in combinations(range(n), k):
        free = [(row, col) for row, pivot in enumerate(pivots)
                for col in range(pivot + 1, n) if col not in pivots]
        for values in product(range(p), repeat=len(free)):
            columns = [[0] * k for _ in range(n)]
            for row, pivot in enumerate(pivots):
                columns[pivot][row] = 1
            for (row, col), value in zip(free, values):
                columns[col][row] = value
            yield columns


def is_isotropic(columns, edges, p):
    row_pairs = list(combinations(range(len(columns[0])), 2))
    return all(
        (columns[x][i] * columns[y][j] - columns[x][j] * columns[y][i]) % p == 0
        for x, y in edges for i, j in row_pairs
    )


def count_isotropic_at_rank(n, tile, p, rank):
    differences = {(x - y) % n for x in tile for y in tile if x != y}
    edges = [(x, y) for x, y in combinations(range(n), 2) if (x - y) % n in differences]
    return sum(is_isotropic(columns, edges, p) for columns in rref_matrices(n, rank, p))


def optimal_packing_stats(n, tile):
    differences = {(x - y) % n for x in tile for y in tile if x != y}
    conflicts = [
        sum(1 << ((i + d) % n) for d in differences)
        for i in range(n)
    ]

    @lru_cache(None)
    def optimum(available):
        if not available:
            return 0, 1
        pivot = (available & -available).bit_length() - 1
        rest = available ^ (1 << pivot)
        without_rank, without_count = optimum(rest)
        with_rank, with_count = optimum(rest & ~conflicts[pivot])
        with_rank += 1
        if with_rank > without_rank:
            return with_rank, with_count
        if without_rank > with_rank:
            return without_rank, without_count
        return with_rank, with_count + without_count

    return optimum((1 << n) - 1)


def check_fiber_rank(n, period, tile):
    """Check the support criterion using all singletons and pairs in one fiber."""
    differences = {(x - y) % n for x in tile for y in tile if x != y}
    fiber_size = n // period
    target_rank = 1 if period != 5 else 2

    def minimum_neighborhood_size(support):
        neighbors = {(x + d) % n for x in support for d in differences}
        sizes = [sum(y % period == s for y in neighbors) for s in range(1, period)]
        return min(size for size in sizes if size)

    fiber = tuple(range(0, n, period))
    assert len(fiber) == fiber_size
    for x in fiber:
        assert minimum_neighborhood_size((x,)) == target_rank
    for x, y in combinations(fiber, 2):
        rank = minimum_neighborhood_size((x, y))
        if (n, period) == (10, 5):
            assert rank == 2
        else:
            assert rank > target_rank


def run_odd():
    fixed_hole_cases = unrestricted_cases = 0
    for b in range(3, 14, 2):
        for a in range(1, b, 2):
            if gcd(a, b) != 1:
                continue
            period = a * b + b - a
            tile = {0, a, b, a + b}
            for n in range(period, 91, period):
                if n <= 2 * (a + b):
                    continue
                holes = set(range(0, n, period))
                target = sum(1 << x for x in range(n) if x not in holes)
                covers = list(all_tilings(n, tile, target))
                assert len(covers) == 1, (n, a, b, len(covers))
                centers, = covers
                rank = n * (period - 1) // (4 * period)
                assert len(centers) == rank
                center_tiles = [{(c + t) % n for t in tile} for c in centers]
                for x in range(n):
                    if x not in centers:
                        candidate = {(x + t) % n for t in tile}
                        assert sum(bool(candidate & block) for block in center_tiles) >= 2
                check_fiber_rank(n, period, tile)
                fixed_hole_cases += 1
                if n <= 30:
                    assert optimal_packing_stats(n, tile) == (rank, period), (n, a, b)
                    unrestricted_cases += 1
    assert count_isotropic_at_rank(10, {0, 1, 3, 4}, 2, 2) == 5
    print(f'Checked {fixed_hole_cases} odd-step cases through modulus 90 by exact cover and fiber rank.')
    print(f'Checked {unrestricted_cases} unrestricted maximum-packing counts through modulus 30.')
    print('Checked the odd case N=10, a=1, b=3 by exhaustive rank-2 RREF over F_2.')


def run():
    tile_cases = tiling_cases = isotope_cases = 0
    for n in range(4, 41):
        for a, b in combinations(range(1, n), 2):
            tile = {0, a, b, (a + b) % n}
            if gcd(gcd(n, a), b) != 1 or len(tile) != 4:
                continue
            covers = set(all_tilings(n, tile))
            expected = predicted_tilings(n, a, b)
            assert covers == expected, (n, a, b, len(covers), len(expected))
            tile_cases += 1
            if not covers:
                continue
            tiling_cases += 1
            if n > 8:
                continue
            stabilizer = sum({(x + t) % n for x in tile} == tile for t in range(n))
            for p in ((2, 3) if n == 4 else (2,)):
                lines = (p**stabilizer - 1) // (p - 1)
                predicted = (len(covers) // stabilizer**(n // 4)) * lines**(n // 4)
                assert count_isotropic_at_rank(n, tile, p, n // 4) == predicted, (n, a, b, p)
                isotope_cases += 1
    print(f'Checked {tile_cases} primitive cyclic tiles with sizes through 40.')
    print(f'{tiling_cases} tile. Exact complement sets match in every case.')
    print(f'Checked {isotope_cases} field/graph instances by exhaustive RREF at the tiling size.')


if __name__ == '__main__':
    run()
    run_odd()


