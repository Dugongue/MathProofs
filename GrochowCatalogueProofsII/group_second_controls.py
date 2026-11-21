"""Small finite checks for the written GP-0459 and GP-0511 constructions."""

from itertools import combinations, permutations, product


def verify_latin_controls():
    checked = 0
    for width in (3, 4, 5):
        n = 1 << width
        changed_bits = set()
        for k in range(width):
            direction = 1 << k
            reps = [i for i in range(n) if not i & direction]
            for a, b in product(reps, repeat=2):
                row_pair = {a, a ^ direction}
                col_pair = {b, b ^ direction}
                support = {(row, col, k) for row, col in product(row_pair, col_pair)}
                assert support.isdisjoint(changed_bits)
                changed_bits.update(support)

                def operation(x, y):
                    return x ^ y ^ (direction if x in row_pair and y in col_pair else 0)

                for row in row_pair:
                    assert len({operation(row, col) for col in range(n)}) == n
                for col in col_pair:
                    assert len({operation(row, col) for row in range(n)}) == n
                z = next(i for i in range(n) if i not in col_pair and (b ^ i) not in col_pair)
                assert operation(operation(a, b), z) != operation(a, operation(b, z))
                checked += 1
        assert len(changed_bits) == width * n * n
    return checked


def apply_linear(image_basis, vector):
    image = 0
    for i, value in enumerate(image_basis):
        if vector & (1 << i):
            image ^= value
    return image


def verify_orbit_cost():
    checked = 0
    for k in (3, 4):
        pairs = list(combinations(range(k), 2))
        basis = [1 << i for i in range(k)]
        pair_forms = [basis[i] | basis[j] for i, j in pairs]
        support = set(basis + pair_forms)
        mappings = []
        for images in permutations(support, k):
            image_support = [apply_linear(images, v) for v in support]
            if set(image_support) == support:
                mappings.append(dict(zip(support, image_support)))
        cycle = {tuple(sorted((i, (i + 1) % k))) for i in range(k)}
        basis_multiplicity = len(pairs) + 3
        first = {v: basis_multiplicity for v in basis}
        first.update({v: 1 + (p in cycle) for p, v in zip(pairs, pair_forms)})
        for edge_flags in product((False, True), repeat=len(pairs)):
            second = {v: basis_multiplicity for v in basis}
            second.update({v: 1 + flag for v, flag in zip(pair_forms, edge_flags)})
            costs = [(sum(abs(first[v] - second[mapping[v]]) for v in support), mapping)
                     for mapping in mappings]
            minimum = min(cost for cost, _ in costs)
            assert all({mapping[v] for v in basis} == set(basis)
                       for cost, mapping in costs if cost == minimum)
            graph_edges = {p for p, flag in zip(pairs, edge_flags) if flag}
            has_ham_cycle = any(all(tuple(sorted((pi[i], pi[(i + 1) % k]))) in graph_edges
                                    for i in range(k)) for pi in permutations(range(k)))
            assert (minimum <= len(graph_edges) - k) == has_ham_cycle
            checked += 1
    return checked


if __name__ == "__main__":
    print("Latin controls:", verify_latin_controls())
    print("Orbit-duplication controls:", verify_orbit_cost())
