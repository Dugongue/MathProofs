"""Exact controls for the separating contractions and cyclic weights."""

from itertools import product


def cyclic_weights(order, layers, exponents):
    return tuple(
        order * exponents[index] - exponents[index - 1]
        for index in range(layers)
    )


def check_weights():
    checked = 0
    for order, layers in product(range(2, 9), range(2, 11)):
        q = order**layers - 1
        reverse = tuple(order ** (layers - index) for index in range(layers))
        assert cyclic_weights(order, layers, reverse) == (order * q,) + (0,) * (layers - 1)
        assert sum(reverse) + q == (2 * order - 1) * q // (order - 1)
        for end in range(-4, 5):
            exponents = tuple(end * order ** (layers - 1 - index) for index in range(layers))
            assert cyclic_weights(order, layers, exponents) == (end * q,) + (0,) * (layers - 1)
            checked += 1
    return checked


def matrix_product(left, right, p):
    return [
        [sum(a * b for a, b in zip(row, col)) % p for col in zip(*right)]
        for row in left
    ]


def cubic_separator(mu, delta, dimension, p):
    vec = [sum(delta.get((i, j, j), 0) for j in range(dimension)) % p
           for i in range(dimension)]
    composition = [[int(i == j) for j in range(dimension)] for i in range(dimension)]
    for _ in range(dimension):
        left = [
            [sum(mu.get((i, j, k), 0) * vec[j] for j in range(dimension)) % p
             for k in range(dimension)]
            for i in range(dimension)
        ]
        composition = matrix_product(left, composition, p)
        vec = [sum(a * b for a, b in zip(row, vec)) % p for row in left]
    return sum(composition[i][i] for i in range(dimension)) % p


def check_cubic():
    checked = 0
    for p in (3, 5, 7, 11, 13, 17, 19):
        for dimension in range(2, min(p, 11)):
            mu, delta = {}, {}
            coefficients = list(range(1, dimension + 1))
            for i, coeff in enumerate(coefficients):
                j = (i + 1) % dimension
                mu[j, i, i] = coeff
                delta[i, i, j] = 1
            expected, factor = 1, 1
            for coeff in coefficients:
                expected = expected * coeff * factor % p
                factor = coeff * factor**2 % p
            q = 2**dimension - 1
            for value in range(p):
                data = delta | {(0, 1, 1): value, (1, 0, 1): value}
                assert cubic_separator(mu, data, dimension, p) == expected * pow(value, q, p) % p
                checked += 1
    return checked


def diagram(order, layers):
    q = order**layers - 1
    x_copies = list(range(q))
    reverse_layers, cursor = [], q
    for i in range(layers):
        next_cursor = cursor + order ** (layers - i)
        reverse_layers.append(list(range(cursor, next_cursor)))
        cursor = next_cursor

    edges = []
    for source, target in zip(x_copies, reverse_layers[0][:-1]):
        edges.extend((source, slot, target, slot) for slot in range(order))
    for previous, current in zip(reverse_layers, reverse_layers[1:]):
        for position, source in enumerate(previous):
            edges.append((source, 0, current[position // order], position % order))
    edges.extend((source, 0, reverse_layers[0][-1], slot)
                 for slot, source in enumerate(reverse_layers[-1]))
    outputs = [(source, slot) for layer in reverse_layers for source in layer
               for slot in range(1, order)]
    inputs = [(target, slot) for target in x_copies for slot in range(order)]
    assert len(outputs) == len(inputs)
    edges.extend((source, out_slot, target, in_slot)
                 for (source, out_slot), (target, in_slot) in zip(outputs, inputs))
    assert len(set((source, slot) for source, slot, _, _ in edges)) == cursor * order
    assert len(set((target, slot) for _, _, target, slot in edges)) == cursor * order
    return x_copies, reverse_layers, edges, cursor


def balanced_terms(order, layers, payload, signed_only=False):
    terms = {}
    for index in range(layers + 1):
        if index and not signed_only:
            terms[(index,) * (2 * order)] = index
    for i in range(1, layers + 1):
        j = i % layers + 1
        for slot in range(order):
            mixed = tuple(j if k == slot else 0 for k in range(order))
            equal = (i,) * order
            if not signed_only:
                terms[equal + mixed] = 1
            terms[mixed + equal] = 1
    if payload:
        terms[(1,) * order + (0,) * order] = payload
    return terms


def contraction_value(order, terms, edges, count):
    # Enumerate compatible colors exactly by restricting the possible local tensor entries.
    outgoing = [[] for _ in range(count)]
    for source, out_slot, target, in_slot in edges:
        outgoing[source].append((out_slot, target, order + in_slot))
        outgoing[target].append((order + in_slot, source, out_slot))

    def solve(domains, pending):
        while pending:
            node = pending.pop()
            for slot, other, other_slot in outgoing[node]:
                colors = {row[slot] for row in domains[node]}
                filtered = tuple(row for row in domains[other] if row[other_slot] in colors)
                if not filtered:
                    return 0
                if len(filtered) < len(domains[other]):
                    domains[other] = filtered
                    pending.append(other)
        undecided = [node for node in range(count) if len(domains[node]) > 1]
        if not undecided:
            value = 1
            for (row,) in domains:
                value *= terms[row]
            return value
        node = min(undecided, key=lambda item: (len(domains[item]), -len(outgoing[item])))
        total = 0
        for row in domains[node]:
            branch = domains.copy()
            branch[node] = (row,)
            total += solve(branch, [node])
        return total

    return solve([tuple(terms)] * count, list(range(count)))


def check_balanced():
    full, rigid = 0, 0
    for order, layers in ((2, 2), (2, 3), (3, 2), (2, 4), (3, 3), (4, 2)):
        x_copies, reverse_layers, edges, count = diagram(order, layers)
        terms = balanced_terms(order, layers, 1, signed_only=True)
        payload = (1,) * order + (0,) * order
        labels = [None] * count
        for node in x_copies:
            labels[node] = payload
        for i, layer in enumerate(reverse_layers, start=1):
            j = i % layers + 1
            for node in layer:
                labels[node] = (j,) + (0,) * (order - 1) + (i,) * order
        assert all(row in terms for row in labels)
        assert all(labels[a][i] == labels[b][order + j] for a, i, b, j in edges)

        # Solve again without the layer/color labels. A zero-free first output forces
        # every X copy, and local matching must force the unique global assignment.
        assert contraction_value(order, terms, edges, count) == 1
        rigid += 1
        if (order, layers) in ((2, 2), (2, 3), (3, 2)):
            left = contraction_value(order, balanced_terms(order, layers, 0), edges, count)
            right = contraction_value(order, balanced_terms(order, layers, 1), edges, count)
            assert right - left == 1
            full += 1
    return full, rigid


def main():
    print(f"cyclic weight identities: {check_weights()}")
    print(f"cubic finite-field evaluations: {check_cubic()}")
    full, rigid = check_balanced()
    print(f"balanced complete contractions: {full}")
    print(f"balanced unique assignments: {rigid}")


if __name__ == "__main__":
    main()
