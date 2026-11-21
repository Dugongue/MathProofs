"""Negative tangent rank certificate for the squarefree third Veronese algebras."""

from collections import defaultdict
from itertools import combinations, combinations_with_replacement


PRIME = 101
EXPECTED = {
    7: {2: (623, 623), 1: (21805, 21770)},
    8: {2: (1568, 1568), 1: (87808, 87752)},
}


def ranks(n, drop):
    """Return (number of unknowns, rank modulo 101) in degree -drop."""
    triples = [sum(1 << i for i in triple) for triple in combinations(range(n), 3)]
    bit_weight = {
        mask: tuple((mask >> i) & 1 for i in range(n)) for mask in [0, *triples]
    }
    variables = range(len(triples))
    overlap_generators = set()
    binomial_generators = {}
    representative = {}
    for a, b in combinations_with_replacement(variables, 2):
        x, y = triples[a], triples[b]
        if x & y:
            overlap_generators.add((a, b))
        elif x | y in representative:
            binomial_generators[a, b] = representative[x | y]
        else:
            representative[x | y] = (a, b)

    target_masks = [0] if drop == 2 else triples
    generators = sorted(overlap_generators | binomial_generators.keys())
    shift = {}
    for a, b in generators:
        for target in target_masks:
            shift[(a, b), target] = tuple(
                out - left - right
                for out, left, right in zip(
                    bit_weight[target], bit_weight[triples[a]], bit_weight[triples[b]]
                )
            )

    pivots = defaultdict(dict)

    def impose(terms):
        """Impose the image of sum(sign * z_i * g) = 0, one row per shift."""
        rows = defaultdict(dict)
        for generator, i, sign in terms:
            for target in target_masks:
                # Squarefree product of z_i with target; any overlap is zero.
                if target & triples[i]:
                    continue
                column = (generator, target)
                row = rows[shift[column]]
                row[column] = (row.get(column, 0) + sign) % PRIME

        for weight, row in rows.items():
            row = {column: value for column, value in row.items() if value}
            weight_pivots = pivots[weight]
            while row:
                column = min(row)
                value = row[column]
                if column not in weight_pivots:
                    inverse = pow(value, -1, PRIME)
                    weight_pivots[column] = {
                        key: entry * inverse % PRIME for key, entry in row.items()
                    }
                    break
                for key, entry in weight_pivots[column].items():
                    new_value = (row.get(key, 0) - value * entry) % PRIME
                    if new_value:
                        row[key] = new_value
                    else:
                        row.pop(key, None)

    def overlap_divisors(a, b, c):
        """Represent a cubic as a variable times a quadratic monomial in I."""
        return list(dict.fromkeys(
            (i, (j, k))
            for i, j, k in [(a, b, c), (b, a, c), (c, a, b)]
            if (j, k) in overlap_generators
        ))

    for cubic in combinations_with_replacement(variables, 3):
        (i, g), *other_divisors = overlap_divisors(*cubic)
        for j, h in other_divisors:
            impose([(g, i, 1), (h, j, -1)])

    for g, h in binomial_generators.items():
        for i in variables:
            j, left = overlap_divisors(*sorted((*g, i)))[0]
            k, right = overlap_divisors(*sorted((*h, i)))[0]
            impose([(g, i, 1), (left, j, -1), (right, k, 1)])

    return len(shift), sum(len(weight_pivots) for weight_pivots in pivots.values())


if __name__ == "__main__":
    for n, cases in EXPECTED.items():
        for drop, expected in cases.items():
            actual = ranks(n, drop)
            assert actual == expected, (n, -drop, actual, expected)
            print(f"n={n}, degree={-drop}: columns={actual[0]}, rank={actual[1]}")
