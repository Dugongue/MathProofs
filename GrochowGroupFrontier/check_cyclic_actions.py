"""Exhaustive small cyclic-center controls for the optimal-index formula."""

from collections import deque
from itertools import product


def group(center_order, tangent_order, a, b):
    d, m = center_order, tangent_order
    elements = list(product(range(m), range(m), range(d)))
    index = {elt: i for i, elt in enumerate(elements)}

    def multiply(left, right):
        x, y, z = left
        u, v, w = right
        return (
            (x + u) % m,
            (y + v) % m,
            (z + w + (d // m) * x * v + a * ((x + u) // m) + b * ((y + v) // m)) % d,
        )

    return [[index[multiply(x, y)] for y in elements] for x in elements]


def largest_center_free_subgroup(table, center_order):
    initial = frozenset((0,))
    checked = {initial}
    frontier = deque([(initial, ())])
    biggest = 1

    while frontier:
        subgroup, generators = frontier.popleft()
        biggest = max(biggest, len(subgroup))
        for element in range(center_order, len(table)):
            if element in subgroup:
                continue
            candidate = set(subgroup)
            queue = deque(subgroup)
            enlarged_generators = (*generators, element)
            while queue:
                current = queue.popleft()
                for gen in enlarged_generators:
                    nxt = table[current][gen]
                    if 0 < nxt < center_order:
                        break
                    if nxt not in candidate:
                        candidate.add(nxt)
                        queue.append(nxt)
                else:
                    continue
                break
            else:
                extension = frozenset(candidate)
                if extension not in checked:
                    checked.add(extension)
                    frontier.append((extension, enlarged_generators))

    return biggest


def main():
    checks = 0
    for d, m in [(2, 2), (4, 2), (4, 4), (8, 2), (3, 3), (9, 3)]:
        for a, b in product(range(d), repeat=2):
            table = group(d, m, a, b)
            optimum = len(table) // largest_center_free_subgroup(table, d)
            expected = d * m * (2 if d == 2 and a == b == 1 else 1)
            assert optimum == expected, (d, m, a, b, optimum, expected)
            checks += 1
    print(f"Verified {checks} explicit group laws against the cyclic-center formula.")


if __name__ == "__main__":
    main()
