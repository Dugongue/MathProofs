"""Construct and test the explicit 29-dimensional multiplication seeds."""
from itertools import product


def multiplication(endpoint):
    vertices = ("0", "1", "a", "b", "2", "w")
    arrows = {**{f"u{i}": ("0", "1") for i in range(3)},
              **{f"v{i}": ("0", "2") for i in range(3)},
              "r": ("w", "1"), "t": ("w", "2"), "eta": ("a", "b"),
              "pa": ("1", "a"), "pb": ("1", "b"),
              "qa": ("a", "2"), "qb": ("b", "2")}

    def ends(path):
        if len(path) == 1 and path[0] in vertices:
            return path[0], path[0]
        return arrows[path[0]][0], arrows[path[-1]][1]

    def concatenate(left, right):
        if ends(left)[1] != ends(right)[0]:
            return None
        if left[0] in vertices:
            return right
        if right[0] in vertices:
            return left
        path = left + right
        if "eta" in path:
            return None
        if len(path) <= 2:
            return path
        assert len(path) == 3
        arrow, arm, _ = path
        if arrow == "r":
            return ("t",)
        maps = {"pa": {"u0": "v1", "u1": "v2"},
                "pb": {"u1": "v2"} if endpoint else {"u0": "v0", "u2": "v2"}}
        value = maps[arm].get(arrow)
        return (value,) if value else None

    short_paths = [(arrow,) for arrow in arrows]
    long_paths = [left + right for left, right in product(short_paths, repeat=2)
                  if concatenate(left, right) is not None]
    basis = [(vertex,) for vertex in vertices] + short_paths + long_paths
    index = {path: i for i, path in enumerate(basis)}
    return basis, {(i, j): index[value] for i, left in enumerate(basis)
                   for j, right in enumerate(basis)
                   if (value := concatenate(left, right)) is not None}


def verify(basis, table, nonzero):
    assert len(basis) == 29 and len(table) == nonzero
    assert len(set(basis)) == 29
    for i in range(len(basis)):
        from_left = [table[e, i] for e in range(6) if (e, i) in table]
        from_right = [table[i, e] for e in range(6) if (i, e) in table]
        assert from_left == from_right == [i]
    for i, j, k in product(range(len(basis)), repeat=3):
        assert table.get((table.get((i, j)), k)) == table.get((i, table.get((j, k))))


if __name__ == "__main__":
    for endpoint, nonzero in ((False, 74), (True, 72)):
        basis, table = multiplication(endpoint)
        verify(basis, table, nonzero)
        print(f"29-dimensional seed with {nonzero} binary coefficients passed 24,389 associativity checks.")

