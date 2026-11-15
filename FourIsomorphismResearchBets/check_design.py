from collections import Counter
from itertools import combinations
from functools import reduce
from operator import xor



V = range(16)
pairs = list(combinations(V, 2))
index = {pair: i for i, pair in enumerate(pairs)}


def bent_seed(x):
    return ((x >> 0) & (x >> 3) & 1) ^ ((x >> 1) & (x >> 2) & 1)


def flat_mask(block):
    return sum(1 << x for x in block)


def direction(block):
    return tuple(sorted(x ^ block[0] for x in block))


affine_flats = [b for b in combinations(V, 4) if reduce(xor, b) == 0]
blocks = [b for b in affine_flats if reduce(xor, map(bent_seed, b)) == 0]
assert len(affine_flats) == 140 and len(blocks) == 60
masks = [sum(1 << index[p] for p in combinations(b, 2)) for b in blocks]
by_pair = [[j for j, mask in enumerate(masks) if mask >> i & 1] for i in range(120)]
assert all(len(choices) == 3 for choices in by_pair)


def covers(remaining, prefix):
    if not remaining:
        yield tuple(sorted(prefix))
        return
    pending = remaining
    best = None
    while pending:
        bit = pending & -pending
        i = bit.bit_length() - 1
        viable = [j for j in by_pair[i] if masks[j] & remaining == masks[j]]
        if not viable:
            return
        if best is None or len(viable) < len(best):
            best = viable
        if len(best) == 1:
            break
        pending ^= bit
    for j in best:
        yield from covers(remaining ^ masks[j], prefix + [j])


def rank(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return len(basis)


def report():
    solutions = list(covers((1 << len(pairs)) - 1, []))
    kinds = Counter()
    examples = {}
    for sol in solutions:
        selected = [blocks[j] for j in sol]
        assert len(selected) == 20
        assert Counter(pair for b in selected for pair in combinations(b, 2)) == Counter(pairs)
        counts = Counter(map(direction, selected))
        key = (len(counts), tuple(sorted(counts.values())), rank(map(flat_mask, selected)))
        kinds[key] += 1
        examples[key] = selected
    print('subdesigns:', len(solutions))
    for key, count in sorted(kinds.items()):
        print('kind:', key, 'count:', count, 'example:', examples[key])
    return solutions





def multiply_in_field(x, y, degree, modulus):
    product = 0
    while y:
        if y & 1:
            product ^= x
        y >>= 1
        x <<= 1
        if x >> degree:
            x ^= modulus
    return product


def assert_recognized(table, dimension):
    from recognize_design import recognize, vanishing_blocks

    point_order = list(reversed(range(len(table))))
    names = [f'p-{i}' for i in point_order]
    renamed = [[f'p-{i}' for i in block] for block in vanishing_blocks(table)]
    outcome = recognize(names, renamed, dimension)
    new_blocks = vanishing_blocks(outcome['truth_table'])
    coordinates = dict(zip(point_order, outcome['point_coordinates']))
    old_blocks = {tuple(sorted(coordinates[i] for i in block)) for block in vanishing_blocks(table)}
    assert new_blocks == old_blocks


def check_reconstruction(solutions):
    from recognize_design import Rejection, extend, recognize, vanishing_blocks

    counts = []
    for degree, modulus in [(1, 3), (2, 7), (3, 11), (4, 19)]:
        field_size = 1 << degree
        table = [multiply_in_field(i % field_size, i // field_size, degree, modulus)
                 for i in range(field_size * field_size)]
        assert_recognized(table, degree)
        if degree > 1:
            original = [value & 1 for value in table]
            extension = extend(original, 1, degree - 1, vanishing_blocks(table))
            assert vanishing_blocks(extension['truth_table']) == vanishing_blocks(table)
        counts.append((2 * degree, degree))
    print('Raw recognition and reconstruction passed for (n, m):', counts)

    original = [bent_seed(x) for x in V]
    for solution in solutions:
        selected = {blocks[j] for j in solution}
        extension = extend(original, 1, 1, selected)
        assert vanishing_blocks(extension['truth_table']) == selected
    print('All six Steiner subdesigns reconstructed from the fixed scalar projection.')

    # Direction list from the explicit classical construction cited in DESIGN.md.
    directions = [(1,6,7), (1,8,9), (1,10,11), (2,4,6), (2,12,14), (2,13,15),
                  (3,4,7), (3,9,10), (3,12,15), (4,10,14), (5,8,13), (5,9,12),
                  (5,11,14), (6,11,13), (7,8,15)]
    singer = {tuple(sorted((x, x ^ a, x ^ b, x ^ c))) for a, b, c in directions for x in V}
    try:
        recognize(list(V), singer, 1)
    except Rejection as exc:
        print('Classical nonrealizable Singer design rejected:', exc)
    else:
        raise AssertionError('Expected the classical Singer control to be rejected.')


if __name__ == '__main__':
    check_reconstruction(report())
