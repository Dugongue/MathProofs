from collections import deque
from itertools import product


def compose(first, second):
    return tuple(first[value] for value in second)


def inverse(perm):
    positions = [0] * len(perm)
    for index, value in enumerate(perm):
        positions[value] = index
    return tuple(positions)


def verify_projected_stabilizer(prime):
    states = tuple(product(range(prime), repeat=2))
    index = {state: i for i, state in enumerate(states)}
    identity = tuple(range(len(states)))

    def permutation(fn):
        return tuple(index[tuple(t % prime for t in fn(x, y))] for x, y in states)

    turn = permutation(lambda x, y: (y, -x))
    shear = permutation(lambda x, y: (x + y, y))
    lower = permutation(lambda x, y: (x, y + x))
    translate = permutation(lambda x, y: (x + 1, y))
    translate_more = permutation(lambda x, y: (x, y + 1))
    choices = [((turn, shear), (shear, turn), (translate, lower)),
               ((translate, turn), (translate_more, shear), (lower, lower)),
               ((turn, lower), (lower, turn), (shear, shear)),
               ((translate, identity), (translate_more, turn), (shear, lower))]

    loops_tested = 0
    for actions in choices:
        for base in (index[0, 0], index[1, 0], index[1, 1]):
            paths = {base: identity}
            frontier = deque([base])
            while frontier:
                state = frontier.popleft()
                for state_action, label in actions:
                    target = state_action[state]
                    if target not in paths:
                        paths[target] = compose(paths[state], label)
                        frontier.append(target)
            projected_edges = {
                compose(compose(path_label, label), inverse(paths[state_action[state]]))
                for state, path_label in paths.items() for state_action, label in actions
            }
            loops_tested += len(paths) * len(actions)

            image_generated = {identity}
            frontier = deque([identity])
            while frontier:
                label = frontier.popleft()
                for edge in projected_edges:
                    extended = compose(label, edge)
                    if extended not in image_generated:
                        image_generated.add(extended)
                        frontier.append(extended)

            joint = {(base, identity)}
            frontier = deque(joint)
            while frontier:
                state, accumulated = frontier.popleft()
                for state_action, label in actions:
                    edge = state_action[state], compose(accumulated, label)
                    if edge not in joint:
                        joint.add(edge)
                        frontier.append(edge)
            exact_image = {label for state, label in joint if state == base}
            assert image_generated == exact_image
    return loops_tested


def verify_weighted_transitions(prime):
    size = 3
    checks = 0
    for exponents in product(range(3), repeat=size):
        degrees = [prime ** exponent for exponent in exponents]
        for row, col in product(range(size), repeat=2):
            if row == col:
                continue
            divisibility = prime ** max(0, exponents[col] - exponents[row])
            for coefficient in range(prime):
                raw = divisibility * coefficient
                assert raw * degrees[row] % degrees[col] == 0
                conjugated = (raw * degrees[row] // degrees[col]) % prime
                images = set()
                for coordinates in product(range(prime), repeat=size):
                    values = list(coordinates)
                    values[row] = (values[row] + conjugated * values[col] + 1) % prime
                    images.add(tuple(values))
                assert len(images) == prime ** size
                checks += 1
    return checks


def verify_central_shifts(order, modulus, power_x, power_y, intersection_order):
    assert modulus % order == 0
    assert modulus % intersection_order == 0
    step = modulus // intersection_order
    assert power_y % step == 0
    elements = tuple(product(range(order), range(order), range(modulus)))
    subgroup = {element for element in elements if element[0] == 0 and element[2] % step == 0}

    def multiply(g, h):
        a, b, z = g
        c, d, w = h
        carry_x, x = divmod(a + c, order)
        carry_y, y = divmod(b + d, order)
        return x, y, (z + w + carry_x * power_x + carry_y * power_y +
                      b * c * (modulus // order)) % modulus

    decisions = 0
    for value_x, value_y in product(range(modulus), repeat=2):
        if order * value_x % modulus or order * value_y % modulus:
            continue

        def shift(element, sign=1):
            x, y, z = element
            return x, y, (z + sign * (x * value_x + y * value_y)) % modulus

        for g in elements:
            assert shift(shift(g), -1) == g
            for h in elements:
                assert shift(multiply(g, h)) == multiply(shift(g), shift(h))
                decisions += 1
        fixes_first = shift((1, 0, 0)) == (1, 0, 0)
        preserves_subgroup = {shift(element) for element in subgroup} == subgroup
        actual_restriction = fixes_first and preserves_subgroup
        assert actual_restriction == (value_x == 0 and value_y % step == 0)
    return decisions


if __name__ == '__main__':
    primes = (2, 3, 5)
    edges = sum(verify_projected_stabilizer(prime) for prime in primes)
    transitions = sum(verify_weighted_transitions(prime) for prime in primes)
    group_cases = [(2, 2, 1, 0, 1), (2, 4, 1, 2, 2), (3, 3, 0, 1, 3),
                   (4, 4, 1, 2, 2), (4, 8, 1, 2, 4)]
    shifts = sum(verify_central_shifts(*case) for case in group_cases)
    print(f'PASS: {edges} projected Schreier edges, {transitions} weighted affine transitions, '
          f'and {shifts} central-shift multiplication cases')
