"""Finite controls for lift compensation and exact tag recovery."""

from itertools import product


def swap(index, pair):
    result = list(index)
    first, second = pair
    result[first], result[second] = result[second], result[first]
    return tuple(result)


def path_to_ordered(index):
    """A path of permitted swaps from this position to its monomial lift."""
    ordered = tuple(sorted(index))
    queue = [(index, [])]
    visited = {index}
    for current, path in queue:
        if current == ordered:
            return path
        for pair in [(1, 2), (0, 2)]:
            next_index = swap(current, pair)
            if next_index not in visited:
                visited.add(next_index)
                queue.append((next_index, path + [(current, next_index, pair)]))
    raise AssertionError("The two swaps must generate every coefficient orbit")


def check_cubic_lifts():
    triples = list(product(range(2), repeat=3))
    canonical = [key for key in triples if tuple(sorted(key)) == key]
    paths = {key: path_to_ordered(key) for key in triples}
    checks = 0
    for entries in product(range(3), repeat=4):
        a, b, c, d = entries
        if (a * d - b * c) % 3 == 0:
            continue
        change = ((a, b), (c, d))
        for coefficients in product(range(3), repeat=len(canonical)):
            lift = dict(zip(canonical, coefficients))
            pulled = {
                (i, j, k): sum(
                    lift[p, q, s] * change[p][i] * change[q][j] * change[s][k]
                    for p, q, s in canonical
                ) % 3
                for i, j, k in triples
            }
            form = dict.fromkeys(triples, 0)
            for key, value in pulled.items():
                form[tuple(sorted(key))] += value
            difference = {key: (form[key] - pulled[key]) % 3 for key in triples}
            correction = {(1, 2): dict.fromkeys(triples, 0),
                          (0, 2): dict.fromkeys(triples, 0)}
            for key in triples:
                for start, end, pair in paths[key]:
                    correction[pair][start] += difference[key]
                    correction[pair][end] -= difference[key]
            for key in triples:
                assert sum(part[key] for part in correction.values()) % 3 == difference[key]
                for pair, part in correction.items():
                    assert (part[key] + part[swap(key, pair)]) % 3 == 0
                    if key[pair[0]] == key[pair[1]]:
                        assert part[key] % 3 == 0
            checks += 1
    assert checks == 81 * 48
    return checks


def add_scaled(target, source, scale, modulus=9):
    for key, value in source.items():
        new_value = (target.get(key, 0) + scale * value) % modulus
        if new_value:
            target[key] = new_value
        else:
            target.pop(key, None)


def determinant(matrix):
    """Fraction-free elimination for the selected integer minors."""
    work = [row[:] for row in matrix]
    sign, previous = 1, 1
    for i in range(len(work) - 1):
        pivot_row = next((j for j in range(i, len(work)) if work[j][i]), None)
        if pivot_row is None:
            return 0
        if pivot_row != i:
            work[i], work[pivot_row] = work[pivot_row], work[i]
            sign *= -1
        pivot = work[i][i]
        for j in range(i + 1, len(work)):
            for k in range(i + 1, len(work)):
                numerator = work[j][k] * pivot - work[j][i] * work[i][k]
                assert numerator % previous == 0
                work[j][k] = numerator // previous
            work[j][i] = 0
        previous = pivot
    return sign * work[-1][-1]


def check_tags():
    # Two one-dimensional original row parts, a single original column.
    groups = (0, 0, 1, 1)
    ranks = (4, 8, 16, 32)
    tags, row_supports, column_supports, private_blocks = [], [], [], []
    next_row, next_column = 6, 5
    for j, (group, rank) in enumerate(zip(groups, ranks)):
        private = [(next_row + k, next_column + k) for k in range(rank)]
        tag = {(group, j + 1): 1, (j + 2, 0): 1}
        tag.update(dict.fromkeys(private, 1))
        tags.append(tag)
        private_blocks.append(private)
        row_supports.append([group, j + 2] + [r for r, _ in private])
        column_supports.append([j + 1, 0] + [s for _, s in private])
        next_row += rank
        next_column += rank

    for i in (0, 1):
        assert set(row_supports[2*i]) & set(row_supports[2*i+1]) == {i}
    assert set(column_supports[0]) & set(column_supports[1]) == {0}
    data = {(0, 0): 3, (1, 0): 1}
    scales = (3, 1, 6, 2)
    units = (2, 4, 5, 8)
    normalized = []
    for j, tag in enumerate(tags):
        combination = {}
        add_scaled(combination, tag, units[j])
        add_scaled(combination, data, scales[j])
        new_slice = combination.copy()
        for i, scale in enumerate(scales):
            unit_inverse = pow(units[i], -1, 9)
            for (row, _), value in data.items():
                for col in range(next_column):
                    entry = combination.get((i + 2, col), 0)
                    add_scaled(new_slice, {(row, col): value}, -scale * unit_inverse * entry)
        assert new_slice == {key: units[j] for key in tag}
        normalized.append(new_slice)

    # Off-tag coefficient 3 disappears mod 3, but a single appended minor sees it mod 9.
    first, other = 0, 1
    polluted = normalized[first].copy()
    add_scaled(polluted, tags[other], 3)
    row, col = private_blocks[other][0]
    selected_rows = row_supports[first] + [row]
    selected_columns = column_supports[first] + [col]
    minor = [[polluted.get((r, s), 0) for s in selected_columns] for r in selected_rows]
    assert determinant(minor) % 9 == (units[first] ** len(row_supports[first]) * 3) % 9
    assert determinant(minor) % 9 == 3
    assert all(value % 3 == 0 for key, value in polluted.items() if key not in normalized[first])

    polluted_data = data.copy()
    add_scaled(polluted_data, tags[other], 3)
    assert polluted_data[row, col] == 3
    assert col not in (0,)
    return next_row, next_column, 1 + len(tags)


print(f"Checked lift compensations for {check_cubic_lifts()} binary cubics and basis changes.")
print(f"Checked unit tag cancellation and nilpotent obstructions in shape {check_tags()} over Z/9.")
