"""Exact reconstruction of a vectorial bent function from explicit blocks."""

from collections import Counter
from itertools import combinations
from pathlib import Path
import argparse
import json


class Rejection(ValueError):
    """The supplied block system fails a recognition check."""


def block_system(points, blocks):
    if len(set(points)) != len(points):
        raise Rejection('Point names must be distinct.')
    position = {label: i for i, label in enumerate(points)}
    normalized = set()
    for block in blocks:
        try:
            row = tuple(sorted(position[label] for label in block))
        except KeyError as exc:
            raise Rejection('A block contains an unknown point.') from exc
        if len(row) != 4 or len(set(row)) != 4 or row in normalized:
            raise Rejection('Expected distinct four-element blocks.')
        normalized.add(row)
    return normalized


def bent_parameters(point_count, output_dimension):
    if point_count < 4:
        raise Rejection('Expected at least four points.')
    n = point_count.bit_length() - 1
    if point_count != 1 << n or n % 2 or not 1 <= output_dimension <= n // 2:
        raise Rejection('Expected 2^n points, even n, and 1 <= m <= n/2.')
    return n, (point_count >> (output_dimension + 1)) - 1


def check_design_parameters(npoints, blocks, pair_degree):
    counts = Counter(pair for block in blocks for pair in combinations(block, 2))
    if pair_degree == 0 and not counts:
        return
    if len(counts) != npoints * (npoints - 1) // 2:
        raise Rejection('Some pairs lie in no blocks.')
    if any(count != pair_degree for count in counts.values()):
        raise Rejection('A pair has the wrong block multiplicity.')


def row_basis(vectors):
    basis = {}
    for v in vectors:
        while v:
            pivot = v.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = v
                break
            v ^= basis[pivot]
    return basis


def block_kernel(point_count, blocks):
    rows = row_basis(sum(1 << i for i in block) for block in blocks)
    pivots = sorted(rows)
    kernel = []
    for free in range(point_count):
        if free in rows:
            continue
        vector = 1 << free
        for pivot in pivots:
            if (rows[pivot] & vector).bit_count() & 1:
                vector |= 1 << pivot
        kernel.append(vector)
    return kernel


def basis_completion(known, candidates):
    prefix = list(known)
    basis = row_basis(prefix)
    assert len(basis) == len(prefix)
    for candidate in candidates:
        v = candidate
        while v and (pivot := v.bit_length() - 1) in basis:
            v ^= basis[pivot]
        if v:
            basis[v.bit_length() - 1] = v
            prefix.append(candidate)
    return prefix[len(known):]


def coordinate_vectors(basis):
    if not basis:
        return {0: 0}
    lookup = {0: 0}
    for i, b in enumerate(basis):
        lookup.update({v ^ b: c | (1 << i) for v, c in lookup.items()})
    return lookup


def recognize(points, blocks, output_dimension):
    """Return an explicit bent truth table and input coordinate for each point."""
    npoints = len(points)
    n, pair_degree = bent_parameters(npoints, output_dimension)
    normalized = block_system(points, blocks)
    check_design_parameters(npoints, normalized, pair_degree)
    kernel = block_kernel(npoints, sorted(normalized))
    if len(kernel) != n + output_dimension + 1:
        raise Rejection(f'Wrong incidence nullity: {len(kernel)}.')
    coordinates = basis_completion([(1 << npoints) - 1], kernel)
    embedded = [sum(((u >> j) & 1) << i for i, u in enumerate(coordinates))
                for j in range(npoints)]
    if len(set(embedded)) != npoints:
        raise Rejection('Two points have the same kernel evaluations.')
    differences = {a ^ b for a, b in combinations(embedded, 2)}
    holes = set(range(1 << (n + output_dimension))) - differences
    hole_basis = list(row_basis(sorted(holes)).values())
    if len(holes) != 1 << output_dimension or len(hole_basis) != output_dimension:
        raise Rejection('Missing pair sums do not form a subspace of dimension m.')
    complement = basis_completion(hole_basis, [1 << i for i in range(n + output_dimension)])
    coordinate_of = coordinate_vectors(complement + hole_basis)
    assigned = [coordinate_of[p] for p in embedded]
    labels = [p & (npoints - 1) for p in assigned]
    table = [0] * npoints
    for code in assigned:
        table[code & (npoints - 1)] = code >> n
    return {'truth_table': table, 'point_coordinates': labels, 'kernel_dimension': len(kernel)}


def vanishing_blocks(table):
    """List graph zero-sum quadruples from equal pair sums."""
    by_difference = {}
    for x, y in combinations(range(len(table)), 2):
        by_difference.setdefault((x ^ y, table[x] ^ table[y]), []).append((x, y))
    return {tuple(sorted(p + q)) for pairs in by_difference.values() for p, q in combinations(pairs, 2)}


def extend(source_table, source_dimension, added_dimension, subdesign):
    """Return a truth table extending the fixed source, or raise Rejection."""
    npoints = len(source_table)
    target_dimension = source_dimension + added_dimension
    n, pair_degree = bent_parameters(npoints, target_dimension)
    if not 1 <= source_dimension or not 1 <= added_dimension:
        raise Rejection('Expected positive source and added dimensions.')
    if any(not 0 <= value < 1 << source_dimension for value in source_table):
        raise Rejection('An original truth-table value exceeds the source dimension.')
    normalized = block_system(list(range(npoints)), subdesign)
    check_design_parameters(npoints, normalized, pair_degree)
    if any(x ^ y ^ z ^ w or source_table[x] ^ source_table[y] ^ source_table[z] ^ source_table[w]
           for x, y, z, w in normalized):
        raise Rejection('A block fails to vanish on the specified projection.')
    for a in range(1, npoints):
        counts = Counter(source_table[x] ^ source_table[x ^ a] for x in range(npoints))
        if len(counts) != 1 << source_dimension or any(v != npoints >> source_dimension for v in counts.values()):
            raise Rejection('The supplied source is not vectorial bent.')
    kernel = block_kernel(npoints, sorted(normalized))
    if len(kernel) != n + target_dimension + 1:
        raise Rejection(f'Wrong incidence nullity: {len(kernel)}.')
    known = [(1 << npoints) - 1]
    known.extend(sum(((x >> i) & 1) << x for x in range(npoints)) for i in range(n))
    known.extend(sum(((source_table[x] >> i) & 1) << x for x in range(npoints))
                 for i in range(source_dimension))
    extra = basis_completion(known, kernel)
    assert len(extra) == added_dimension
    target = [value | sum(((b >> x) & 1) << (source_dimension + i) for i, b in enumerate(extra))
              for x, value in enumerate(source_table)]
    for a in range(1, npoints):
        counts = Counter(target[x] ^ target[x ^ a] for x in range(npoints))
        if len(counts) != 1 << target_dimension or any(v != npoints >> target_dimension for v in counts.values()):
            raise Rejection('The block kernel forces additional vanishing flats.')
    return {'truth_table': target, 'kernel_dimension': len(kernel)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=['recognize', 'extend'])
    parser.add_argument('input', type=Path)
    args = parser.parse_args()
    data = json.loads(args.input.read_text(encoding='utf-8-sig'))
    try:
        result = (recognize(data['points'], data['blocks'], data['output_dimension'])
                  if args.mode == 'recognize' else
                  extend(data['source_table'], data['source_dimension'], data['added_dimension'], data['blocks']))
    except Rejection as exc:
        print(json.dumps({'accepted': False, 'reason': str(exc)}, indent=2))
        return 1
    print(json.dumps({'accepted': True, **result}, indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
