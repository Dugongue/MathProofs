"""Exact controls for the scalar-tensor separation over prime fields."""

from itertools import combinations, product


def rank_columns(columns, prime):
    """Compute the column rank by elimination in the input coordinate order."""
    pivots = {}
    for vector in columns:
        vector = list(vector)
        for index in range(len(vector)):
            value = vector[index]
            if value == 0:
                continue
            if index not in pivots:
                inverse = pow(value, -1, prime)
                pivots[index] = [(inverse * entry) % prime for entry in vector]
                break
            pivot = pivots[index]
            vector = [(a - value * b) % prime for a, b in zip(vector, pivot)]
    return len(pivots)


def matrix_unit_image(x, column, scalar, prime):
    """Return B(x,e_column) in the quotient by diag(scalar,scalar,1,1)."""
    entries = [x[i] if j == column else 0 for i in range(4) for j in range(4)]
    basis = [0] * 16
    for index, value in zip((0, 5, 10, 15), (scalar, scalar, 1, 1)):
        basis[index] = value
    coefficient = entries[15]
    return tuple((entry - coefficient * b) % prime for entry, b in zip(entries, basis))[:15]


def projective_vectors(prime):
    for lead in range(4):
        for tail in product(range(prime), repeat=3 - lead):
            yield (0,) * lead + (1,) + tail


def check_intersections(prime):
    expected_lines = 1 + prime + prime**2 + prime**3
    result = []
    for scalar in (0, 1):
        spaces = [
            [matrix_unit_image(x, j, scalar, prime) for j in range(4)]
            for x in projective_vectors(prime)
        ]
        assert len(spaces) == expected_lines
        assert all(rank_columns(space, prime) == 4 for space in spaces)
        intersection_pairs = sum(rank_columns(a + b, prime) < 8 for a, b in combinations(spaces, 2))
        result.append(intersection_pairs)
    assert result[0] > 0
    assert result[1] == 0
    print(f"p={prime}, projective codeword lines={expected_lines}, intersection pairs={result}")


def replicated_columns(columns, copies):
    base_rows = len(columns[0])
    return [
        (0,) * (copy * base_rows) + column + (0,) * ((copies - 1 - copy) * base_rows)
        for copy in range(copies)
        for column in columns
    ]


def test_coset(prime, copies):
    """Enumerate the codewords in one rank-one coset at each scalar input."""
    column_count = 4 * copies
    rank_counts = []
    for scalar in (0, 1):
        witness = matrix_unit_image((0, 0, 1, 0), 2, scalar, prime)
        u = witness + (0,) * (len(witness) * (copies - 1))
        # This functional is nonzero on e_2 and e_3 in the first copy.
        v = (0, 0, 1, 1) + (0,) * (column_count - 4)
        perturbation = [tuple((coefficient * value) % prime for value in u) for coefficient in v]
        cases = []
        for x in product(range(prime), repeat=4):
            a = replicated_columns([matrix_unit_image(x, j, scalar, prime) for j in range(4)], copies)
            columns = [tuple((entry + step) % prime for entry, step in zip(col, update))
                       for col, update in zip(a, perturbation)]
            cases.append(rank_columns(columns, prime))
        assert cases.count(1) == 1
        rank_counts.append(cases.count(column_count - 1))

    assert rank_counts[0] >= 2
    assert rank_counts[1] <= 1
    print(f"p={prime}, copies={copies}, rank-{column_count - 1} counts={rank_counts}")



def add_matrices(left, right, prime):
    return [tuple((a + b) % prime for a, b in zip(x, y)) for x, y in zip(left, right)]


def outer_columns(u, v, prime):
    return [tuple(coefficient * entry % prime for entry in u) for coefficient in v]


def compact_adjacent(matrix, basis, copies, prime):
    """Test the forced candidates in the replicated block layout."""
    rows = len(basis[0][0])
    columns = len(basis[0])
    flattened_basis = [tuple(entry for column in vector for entry in column) for vector in basis]

    def block(i, j):
        return [matrix[j * columns + b][i * rows : (i + 1) * rows] for b in range(columns)]

    def candidates():
        for i in range(copies):
            for j in range(copies):
                if i == j:
                    continue
                for b, column in enumerate(block(i, j)):
                    for a, pivot in enumerate(column):
                        if not pivot:
                            continue
                        k = next(index for index in range(copies) if index not in (i, j))
                        u = block(k, j)[b]
                        v = [col[a] for col in block(i, k)]
                        v = [value * pow(pivot, -1, prime) % prime for value in v]
                        negative = [tuple(-entry for entry in col) for col in block(k, k)]
                        yield add_matrices(outer_columns(u, v, prime), negative, prime)
                        return
        for i in range(copies):
            yield [tuple(-entry % prime for entry in col) for col in block(i, i)]

    for correction in candidates():
        flat = tuple(entry for column in correction for entry in column)
        if rank_columns(flattened_basis + [flat], prime) != len(basis):
            continue
        updated = add_matrices(matrix, replicated_columns(correction, copies), prime)
        if rank_columns(updated, prime) == 1:
            return True
    return False


def check_adjacency(prime, copies):
    """Compare the block rule with enumeration of all codeword translates."""
    unit = lambda index, size: tuple(int(index == i) for i in range(size))
    result = []
    for scalar in (0, 1):
        basis = [[matrix_unit_image(unit(i, 4), j, scalar, prime) for j in range(4)] for i in range(4)]
        code = [
            replicated_columns([matrix_unit_image(x, j, scalar, prime) for j in range(4)], copies)
            for x in product(range(prime), repeat=4)
        ]
        rows, columns = 15 * copies, 4 * copies
        same_block = outer_columns(unit(1, rows), unit(0, columns), prime)
        different_blocks = outer_columns(unit(1, rows), unit(5, columns), prime)
        spread = outer_columns(tuple([1] * rows), tuple([1, 0] * (columns // 2)), prime)
        rank_two = add_matrices(same_block, outer_columns(unit(2, rows), unit(1, columns), prime), prime)
        rank_two_offdiag = add_matrices(
            different_blocks, outer_columns(unit(2, rows), unit(6, columns), prime), prime
        )
        inputs = [same_block, different_blocks, spread, rank_two, rank_two_offdiag, code[0]]
        expected_labels = [True, True, True, False, False, False]
        for matrix, expected in zip(inputs, expected_labels):
            for representative in (matrix, add_matrices(matrix, code[-1], prime)):
                exact = any(rank_columns(add_matrices(representative, word, prime), prime) == 1 for word in code)
                assert exact == expected
                assert compact_adjacent(representative, basis, copies, prime) == exact
        result.append(2 * len(inputs))
    print(f"p={prime}, adjacency cases checked={sum(result)}")


if __name__ == "__main__":
    for field_prime in (2, 3, 5):
        check_intersections(field_prime)
        test_coset(field_prime, copies=3)
        check_adjacency(field_prime, copies=3)
