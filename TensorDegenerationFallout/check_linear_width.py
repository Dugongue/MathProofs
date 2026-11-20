"""Exact finite replays of the three-copy anchor section."""

import random


def identity(size):
    return [[int(i == j) for j in range(size)] for i in range(size)]


def transpose(matrix):
    return [list(column) for column in zip(*matrix)]


def multiply(left, right, prime):
    return [[sum(a * b for a, b in zip(row, col)) % prime
             for col in zip(*right)] for row in left]


def inverse(matrix, prime):
    size = len(matrix)
    augmented = [row[:] + unit for row, unit in zip(matrix, identity(size))]
    for i in range(size):
        pivot = next((j for j in range(i, size) if augmented[j][i]), None)
        if pivot is None:
            raise ValueError("singular matrix")
        augmented[i], augmented[pivot] = augmented[pivot], augmented[i]
        row = augmented[i]
        augmented[i] = [(entry * pow(row[i], -1, prime)) % prime for entry in row]
        for j in range(size):
            if i != j:
                multiplier = augmented[j][i]
                augmented[j] = [(a - multiplier * b) % prime
                                for a, b in zip(augmented[j], augmented[i])]
    return [row[size:] for row in augmented]


def random_invertible(size, prime, random_source):
    while True:
        candidate = [[random_source.randrange(prime) for _ in range(size)]
                     for _ in range(size)]
        try:
            inverse(candidate, prime)
        except ValueError:
            continue
        return candidate


def block_bounds(dimensions):
    boundaries = [0]
    for dimension in dimensions:
        boundaries.append(boundaries[-1] + dimension)
    return list(zip(boundaries[:-1], boundaries[1:]))


def transport_block(block, left, right, output, prime):
    row_coordinates = inverse(left, prime)
    col_coordinates = inverse(right, prime)
    old = [[sum(block[u][v][j] * row_coordinates[u][a] * col_coordinates[v][b]
                for u in range(len(left)) for v in range(len(right))) % prime
            for j in range(len(output))]
           for a in range(len(left)) for b in range(len(right))]
    new = transpose(multiply(output, transpose(old), prime))
    return [[new[a * len(right) + b] for b in range(len(right))]
            for a in range(len(left))]


def replay(prime, seed):
    random_source = random.Random(seed)
    x_sizes = [1, 2, 2, 2, 2, 2]
    reference = {3: 1, 4: 2, 5: 1}
    occurrence_line = {3: 6, 4: 7, 5: 8}
    y_sizes = x_sizes + [1, 1, 1]
    bounds = block_bounds(x_sizes)
    total = sum(x_sizes)

    def vector(index, coordinate):
        return [int(j == bounds[index][0] + coordinate) for j in range(total)]

    anchor = {(0, 0): [[vector(0, 0)]]}
    for i in range(1, len(x_sizes)):
        anchor[i, 0] = [[vector(i, a)] for a in range(x_sizes[i])]
        anchor[0, i] = [[vector(i, a) for a in range(x_sizes[i])]]
    for u, line in occurrence_line.items():
        anchor[0, line] = [[vector(0, 0)]]
        anchor[u, line] = [[vector(reference[u], a)] for a in range(x_sizes[u])]
    zero = [0] * total
    anchor[1, 2] = [[vector(0, 0) if a == b else zero for b in range(2)]
                    for a in range(2)]

    left = [random_invertible(size, prime, random_source) for size in x_sizes]
    right = [random_invertible(size, prime, random_source) for size in y_sizes]
    output = random_invertible(total, prime, random_source)
    marked = {(i, j): transport_block(block, left[i], right[j], output, prime)
              for (i, j), block in anchor.items()}
    r_frames = [transpose([row[0] for row in marked[i, 0]])
                for i in range(len(x_sizes))]
    r_whole = [sum((frame[row] for frame in r_frames), []) for row in range(total)]
    inv_r = inverse(r_whole, prime)

    def restrict_coords(columns, which):
        coords = multiply(inv_r, columns, prime)
        first, last = bounds[which]
        assert all(not any(row) for row in coords[:first] + coords[last:])
        return coords[first:last]

    l_to_y = [
        inverse(restrict_coords(transpose(marked[0, i][0]), i), prime)
        for i in range(len(x_sizes))
    ]
    scalars = {line: inverse(restrict_coords(transpose(marked[0, line][0]), 0), prime)
               for line in occurrence_line.values()}
    evaluation = [[restrict_coords(transpose([value]), 0)[0][0]
                   for value in row] for row in marked[1, 2]]
    new_left = [identity(1), identity(2),
                inverse(multiply(evaluation, l_to_y[2], prime), prime)]
    for u, line in occurrence_line.items():
        target = reference[u]
        columns = transpose([[entry * scalars[line][0][0] % prime for entry in row[0]]
                             for row in marked[u, line]])
        copy_in_reference = restrict_coords(columns, target)
        new_left.append(multiply(inverse(copy_in_reference, prime), new_left[target], prime))
    new_right = [multiply(l_to_y[i], new_left[i], prime) for i in range(len(x_sizes))]
    new_right.extend(scalars[i] for i in range(len(x_sizes), len(y_sizes)))
    z_frames = [multiply(frame, basis, prime) for frame, basis in zip(r_frames, new_left)]
    new_z = [sum((frame[row] for frame in z_frames), []) for row in range(total)]
    for (i, j), block in anchor.items():
        assert transport_block(block, new_left[i], new_right[j], new_z, prime) == marked[i, j]


if __name__ == "__main__":
    for p in (2, 3, 5):
        for index in range(12):
            replay(p, index)
    print("36 exact mixed anchor normalizations passed over F2, F3 and F5.")

