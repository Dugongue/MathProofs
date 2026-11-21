"""Exhaustive genus-one rotor-routing control for TopologyBridge.md."""

from itertools import product


def cactus(triangles):
    """The neighbors are listed in rotation order, with their binary voltages."""
    neighbors = [[] for _ in range(1 + 2 * triangles)]
    for i in range(triangles):
        a = 2 * i + 1
        b = a + 1
        neighbors[0].extend(((a, 0), (b, 1)))
        neighbors[a].extend(((0, 0), (b, 0)))
        neighbors[b].extend(((a, 0), (0, 1)))
    return neighbors


def double_cover(neighbors):
    return [
        [2 * target + (sheet ^ voltage) for target, voltage in star]
        for star in neighbors
        for sheet in range(2)
    ]


def faces(neighbors):
    pending = {
        (vertex, index)
        for vertex, star in enumerate(neighbors)
        for index in range(len(star))
    }
    count = 0
    while pending:
        dart = next(iter(pending))
        count += 1
        while dart in pending:
            pending.remove(dart)
            vertex, index = dart
            target = neighbors[vertex][index]
            reverse = neighbors[target].index(vertex)
            dart = (target, (reverse + 1) % len(neighbors[target]))
    return count


def rooted_forest_count(neighbors, sinks):
    """Compute the reduced Laplacian determinant by fraction-free elimination."""
    nonsinks = [v for v in range(len(neighbors)) if v not in sinks]
    matrix = [
        [len(neighbors[v]) if v == w else -neighbors[v].count(w) for w in nonsinks]
        for v in nonsinks
    ]
    previous = 1
    for i in range(len(matrix) - 1):
        pivot = matrix[i][i]
        if pivot <= 0:
            raise AssertionError("The Dirichlet Laplacian must be positive definite")
        for row in range(i + 1, len(matrix)):
            for column in range(i + 1, len(matrix)):
                numerator = (
                    matrix[row][column] * pivot - matrix[row][i] * matrix[i][column]
                )
                quotient, remainder = divmod(numerator, previous)
                assert remainder == 0
                matrix[row][column] = quotient
        previous = pivot
    return matrix[-1][-1] if matrix else 1


def route(neighbors, sinks, rotors, source):
    updated = rotors.copy()
    vertex = source
    while vertex not in sinks:
        updated[vertex] = (updated[vertex] + 1) % len(neighbors[vertex])
        vertex = neighbors[vertex][updated[vertex]]
    return updated


# On one triangle cut open at the sink, the two nonsink rotors have
# these three acyclic states. They are listed in chip-addition order at a.
STATES = ((0, 1), (0, 0), (1, 1))


def encode(coordinates, vertex_pairs, vertex_count):
    rotors = [0] * vertex_count
    for (a, b), coordinate in zip(vertex_pairs, coordinates, strict=True):
        rotors[a], rotors[b] = STATES[coordinate]
    return rotors


def decode(rotors, vertex_pairs):
    return tuple(STATES.index((rotors[a], rotors[b])) for a, b in vertex_pairs)


def project(coordinates):
    return tuple(
        (2 * (coordinates[i] + coordinates[i + 1])) % 3
        for i in range(0, len(coordinates), 2)
    )


def main():
    triangles = 3
    labeled = cactus(triangles)
    base = [[v for v, _ in star] for star in labeled]
    upstairs = double_cover(labeled)
    base_pairs = [(2 * i + 1, 2 * i + 2) for i in range(triangles)]
    lift_pairs = [
        (2 * a + sheet, 2 * b + sheet)
        for a, b in base_pairs
        for sheet in range(2)
    ]
    base_sink = {0}
    sink_fiber = {0, 1}
    vertices = len(upstairs)
    edges = sum(map(len, upstairs)) // 2
    face_count = faces(upstairs)
    assert (vertices, edges, face_count) == (14, 18, 4)
    assert rooted_forest_count(base, base_sink) == 27
    assert rooted_forest_count(upstairs, sink_fiber) == 729
    assert rooted_forest_count(upstairs, {2, 3}) == 2025
    fixed = transitions = 0

    for state in product(range(3), repeat=len(lift_pairs)):
        projection = project(state)
        sheet_exchange = tuple(state[i ^ 1] for i in range(len(state)))
        assert project(sheet_exchange) == projection
        if state == sheet_exchange:
            fixed += 1
            assert projection == state[::2]

        lifted = encode(state, lift_pairs, vertices)
        downstairs = encode(projection, base_pairs, len(base))
        for source in range(2, vertices):
            lifted_result = route(upstairs, sink_fiber, lifted, source)
            projected_result = project(decode(lifted_result, lift_pairs))
            twice = route(base, base_sink, downstairs, source // 2)
            twice = route(base, base_sink, twice, source // 2)
            assert projected_result == decode(twice, base_pairs)
            transitions += 1

    assert (fixed, transitions) == (27, 8748)
    print("Genus 1, 729 wired forests, 27 fixed forests, 8748 verified additions.")
    print("An outer sink fiber has 2025 wired forests.")


if __name__ == "__main__":
    main()
