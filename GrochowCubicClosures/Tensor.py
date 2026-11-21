"""Exact finite control for the maximal-minor argument."""

from itertools import product


def marker_pencil():
    """Two one-dimensional row parts, one old column, and four tags."""
    tags = []
    rows = []
    columns = []
    private_rows = []
    private_columns = []
    next_row, next_column = 6, 5
    for tag, rank in enumerate((1, 2, 3, 4)):
        row_block = list(range(next_row, next_row + rank))
        col_block = list(range(next_column, next_column + rank))
        tags.append(
            [(tag // 2, tag + 1), (tag + 2, 0)]
            + list(zip(row_block, col_block))
        )
        rows.append([tag // 2, tag + 2] + row_block)
        columns.append([0, tag + 1] + col_block)
        private_rows += row_block
        private_columns += col_block
        next_row += rank
        next_column += rank
    return tags, rows, columns, private_rows, private_columns, next_row, next_column


def rank_mod_3(matrix):
    matrix = [row.copy() for row in matrix]
    height, width = len(matrix), len(matrix[0])
    rank = 0
    for column in range(width):
        pivot = next((row for row in range(rank, height) if matrix[row][column]), None)
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = matrix[rank][column]
        for row in range(rank + 1, height):
            coefficient = matrix[row][column] * inverse
            if coefficient:
                for index in range(column, width):
                    matrix[row][index] = (
                        matrix[row][index] - coefficient * matrix[rank][index]
                    ) % 3
        rank += 1
    return rank


def check_marker_pencil():
    tags, rows, columns, private_rows, private_columns, height, width = marker_pencil()
    respective_ranks = (1, 2, 3, 4)
    for part in (0, 1):
        assert set(rows[2 * part]) & set(rows[2 * part + 1]) == {part}
    assert set(columns[0]) & set(columns[1]) == {0}

    # Track the variable label of each entry in a selected maximal minor.
    entries = {(0, 0): "z", (1, 0): "z"}
    for tag, positions in enumerate(tags):
        for position in positions:
            assert position not in entries
            entries[position] = tag
    exponents = []
    for omitted in range(4):
        representatives = [next(j for j in pair if j != omitted)
                           for pair in ((0, 1), (2, 3))]
        y_copy = next(j for j in range(4) if j != omitted)
        selected_rows = [0, 1, y_copy + 2] + private_rows
        selected_cols = [j + 1 for j in representatives] + [0] + private_columns
        assert len(selected_rows) == len(selected_cols) == 13
        assert all((row, col) not in entries
                   for i, row in enumerate(selected_rows) for col in selected_cols[:i])
        labels = [entries[row, col] for row, col in zip(selected_rows, selected_cols)]
        counts = tuple(labels.count(j) for j in range(4))
        assert counts[omitted] == respective_ranks[omitted]
        exponents.append(counts)
    assert tuple(min(column) for column in zip(*exponents)) == respective_ranks

    checked = 0
    for z, *coefficients in product(range(3), repeat=5):
        matrix = [[0] * width for _ in range(height)]
        matrix[0][0] = matrix[1][0] = z
        used = [j for j, coefficient in enumerate(coefficients) if coefficient]
        for j in used:
            for row, col in tags[j]:
                matrix[row][col] = coefficients[j]
        expected = sum(respective_ranks[j] for j in used)
        expected += 1 + len({j // 2 for j in used}) if used else int(z != 0)
        assert rank_mod_3(matrix) == expected
        checked += 1
    assert checked == 243
    return height, width, checked


height, width, checked = check_marker_pencil()
print(f"Checked {checked} F3 slices, four maximal minors, and twin intersections "
      f"in a {height}x{width} pencil.")
