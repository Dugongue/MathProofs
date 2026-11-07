"""Independent fixtures and certificate checks; no calls to core arithmetic."""
from itertools import product


def walsh(truth):
    # Direct character sums: intentionally independent of the optimized FWHT.
    return [sum((1 if (f ^ ((u & x).bit_count() & 1)) == 0 else -1)
                for x, f in enumerate(truth)) for u in range(len(truth))]


def support_design(truth):
    spectrum = walsh(truth)
    support = [u for u, w in enumerate(spectrum) if w]
    return [[((u & x).bit_count() & 1) ^ truth[x] ^ int(spectrum[u] < 0)
             for x in range(len(truth))] for u in support]


def quadratic_truth(m):
    assert m % 2 == 0
    return [sum(((x >> i) & 1) * ((x >> (i + 1)) & 1)
                for i in range(0, m, 2)) % 2 for x in range(1 << m)]


def cubic_plateaued_truth(extra_pairs=0):
    # x0*y0+x1*y1+x0*y1*y2, followed by independent bent pairs.
    m = 5 + 2 * extra_pairs
    truth = []
    for x in range(1 << m):
        b = [(x >> j) & 1 for j in range(m)]
        f = b[0] * b[2] ^ b[1] * b[3] ^ b[0] * b[3] * b[4]
        for j in range(5, m, 2):
            f ^= b[j] * b[j + 1]
        truth.append(f)
    return truth


def sum_free_counterexample():
    pi = [1, 2, 4, 8, 15, 17, 18, 20]
    cols = []
    for z in range(8):
        for w in range(16):
            u = [(w >> j) & 1 for j in range(4)]
            coords = [
                [0, u[0], u[1], u[2], u[3]],
                [u[0], 0, u[1], u[2], u[3]],
                [u[0], u[1], 0, u[2], u[3]],
                [u[0], u[1], u[2], 0, u[3]],
                [u[0] ^ u[1] ^ u[2], u[0], u[1], u[2], u[3]],
                [u[3], u[0], u[1], u[2], u[3]],
                [u[0], u[3], u[1], u[2], u[3]],
                [u[0], u[1], u[3], u[2], u[3]],
            ][z]
            cols.append((z, sum(v << i for i, v in enumerate(coords))))
    return [[((pi[y] & c).bit_count() ^ (b & (y ^ z)).bit_count()) & 1
             for z, c in cols] for y in range(8) for b in range(8)]


def binary_rank(values):
    pivots = {}
    for value in values:
        while value:
            bit = value.bit_length() - 1
            if bit in pivots:
                value ^= pivots[bit]
            else:
                pivots[bit] = value
                break
    return len(pivots)


def check_certificate(matrix, cert):
    """Return (valid, reason), independently checking the realization definition."""
    if not isinstance(cert, dict):
        return False, 'certificate is not a dictionary'
    try:
        truth = cert['truth_table']
        coords = cert['block_coordinates']
        frequencies = cert['point_frequencies']
        offsets = cert['point_offsets']
        amplitude = cert['amplitude']
        size = len(truth)
        if not size or size & (size - 1):
            return False, 'truth table size'
        m = size.bit_length() - 1
        if any(type(x) is not int or x not in (0, 1) for x in truth + offsets):
            return False, 'Boolean values'
        if amplitude <= 0 or type(amplitude) is not int:
            return False, 'amplitude'
        if len(coords) != size or sorted(coords) != list(range(size)):
            return False, 'block coordinates are not a bijection'
        if len(frequencies) != len(matrix) or len(offsets) != len(matrix):
            return False, 'point counts'
        if len(set(frequencies)) != len(frequencies):
            return False, 'repeated frequencies'
        if any(type(u) is not int or not 0 <= u < size for u in frequencies):
            return False, 'frequency bounds'
        spectrum = walsh(truth)
        if any(w not in (0, amplitude, -amplitude) for w in spectrum):
            return False, 'Walsh spectrum'
        if set(frequencies) != {u for u, w in enumerate(spectrum) if w}:
            return False, 'support mismatch'
        for p, (row, u, g) in enumerate(zip(matrix, frequencies, offsets)):
            if len(row) != size:
                return False, 'row length'
            if spectrum[u] != amplitude * (1 - 2 * g):
                return False, 'Walsh signs'
            for b, x in enumerate(coords):
                expected = ((u & x).bit_count() & 1) ^ truth[x] ^ g
                if row[b] != expected:
                    return False, 'incidence identity'
        origin = frequencies[0]
        if binary_rank([u ^ origin for u in frequencies]) != m:
            return False, 'nontrivial linear structures'
        return True, 'all realization conditions verified'
    except (KeyError, TypeError, ValueError, IndexError):
        return False, 'malformed certificate'
