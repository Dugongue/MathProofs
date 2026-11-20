from collections import defaultdict
from itertools import product


def build_path_algebra(coefficients, prime, tails=0):
    # One word of length one and three scalar tags, with six-arrow maximum.
    core_vertices = ("h", "v", "A", "B", "C")
    arrows = {}
    for name in core_vertices[1:]:
        return_arrow = ("return", name)
        arrows[return_arrow] = (name, "h")
        width = len(coefficients) if name == "v" else 1
        for label in range(width):
            arrows[(name, label)] = ("h", name)
    outgoing = {v: [edge for edge, (src, _) in arrows.items() if src == v] for v in core_vertices}
    endpoints = {(v, ()): v for v in core_vertices}
    frontier = list(endpoints)
    for _ in range(6):
        next_frontier = []
        for start, path in frontier:
            end = endpoints[(start, path)]
            for edge in outgoing[end]:
                next_path = (start, path + (edge,))
                endpoints[next_path] = arrows[edge][1]
                next_frontier.append(next_path)
        frontier = next_frontier

    def cycles(*names):
        return ("h", tuple(edge for name, label in names
                           for edge in ((name, label), ("return", name))))

    removed = cycles(("C", 0), ("B", 0), ("A", 0))
    rewrite = {cycles(("v", j), ("A", 0), ("B", 0)): (-c) % prime
               for j, c in enumerate(coefficients) if c % prime}
    assert removed in endpoints and all(path in endpoints for path in rewrite)
    core_paths = [path for path in endpoints if path != removed]
    table = {}
    starts = defaultdict(list)
    for path in core_paths:
        starts[path[0]].append(path)
    for left in core_paths:
        for right in starts[endpoints[left]]:
            path = (left[0], left[1] + right[1])
            if path in endpoints:
                data = rewrite if path == removed else {path: 1}
                if data:
                    table[(left, right)] = data

    basis = list(core_paths)
    for i in range(tails):
        source = (f"tail-{i}", ())
        arrow = (f"tail-{i}", (("tail", i),))
        basis.extend((source, arrow))
        table[(source, source)] = {source: 1}
        table[(source, arrow)] = {arrow: 1}
        table[(arrow, ("h", ()))] = {arrow: 1}
    return basis, table


def check_associative(table, prime):
    starts = defaultdict(list)
    ends = defaultdict(list)
    for (a, b), values in table.items():
        starts[a].append((b, values))
        ends[b].append((a, values))

    def add(total, key, coefficient):
        total[key] = (total[key] + coefficient) % prime
        if not total[key]:
            del total[key]

    left, right = defaultdict(int), defaultdict(int)
    for (a, b), values in table.items():
        for mid, weight in values.items():
            for c, output in starts[mid]:
                for y, c_y in output.items():
                    add(left, (a, b, c, y), weight * c_y)
            for z, output in ends[mid]:
                for y, c_y in output.items():
                    add(right, (z, a, b, y), weight * c_y)
    assert left == right
    return len(left)


def check_scalar_idempotents(prime):
    # Central idempotents of the two-vertex arrow algebra and its scalar product.
    for scalar_count in range(3):
        n = 3 + scalar_count
        rows = [(0, 0, 0), (1, 1, 1), (0, 2, 2), (2, 1, 2)]
        rows.extend((i, i, i) for i in range(3, n))
        basis = [tuple(int(i == j) for i in range(n)) for j in range(n)]

        def multiply(left, right):
            result = [0] * n
            for i, j, k in rows:
                result[k] += left[i] * right[j]
            return tuple(x % prime for x in result)

        central_idempotents = []
        for x in product(range(prime), repeat=n):
            if multiply(x, x) == x and all(multiply(x, y) == multiply(y, x) for y in basis):
                central_idempotents.append(x)
        expected = [(x, x, 0, *tail) for x in (0, 1) for tail in product((0, 1), repeat=scalar_count)]
        assert sorted(central_idempotents) == sorted(expected)
        for idempotent in central_idempotents:
            for v in basis:
                left, right = multiply(idempotent, v), multiply(v, idempotent)
                derivative = tuple((a + b - c) % prime for a, b, c in zip(left, right, v))
                twice = multiply(idempotent, derivative)
                derivative_again = tuple((2 * a - b) % prime for a, b in zip(twice, derivative))
                assert derivative_again == v


if __name__ == "__main__":
    fixtures = triples = 0
    for prime in (2, 3, 5):
        check_scalar_idempotents(prime)
        for coefficients in ((0,), (1,), (1, 2), (0, 1)):
            core, old_products = build_path_algebra(coefficients, prime)
            for tails in (0, 1, 4):
                basis, table = build_path_algebra(coefficients, prime, tails)
                assert len(basis) == len(core) + 2 * tails
                assert len(table) == len(old_products) + 3 * tails
                assert len(old_products) <= 7 * (len(core) + 1)
                triples += check_associative(table, prime)
                fixtures += 1
    print(f"Checked rank-certificate counts and associativity in {fixtures} path algebras.")
    print(f"Verified {triples} nonzero associative output coefficients.")
    print("Checked scalar factors and the idempotent lifting derivative over F2, F3, and F5.")
