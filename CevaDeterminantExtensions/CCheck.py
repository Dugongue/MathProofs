
"""Finite checks of base change, depth profiles, and prescribed character fibers."""

from collections import Counter
from itertools import product
from math import gcd, lcm, prod


def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for smaller in partitions(rest):
        yield ((first,), *smaller)
        for i, block in enumerate(smaller):
            yield (*smaller[:i], (first, *block), *smaller[i + 1:])


def group(moduli):
    return list(product(*(range(modulus) for modulus in moduli)))


def reduce(value, moduli):
    return tuple(a % m for a, m in zip(value, moduli))


def axis_actions(components, moduli):
    values = group(moduli)
    size = sum(map(len, components))
    free_blocks = [block for block in components if 0 not in block]
    for free_values in product(values, repeat=len(free_blocks)):
        action = [values[0]] * size
        for block, value in zip(free_blocks, free_values):
            for v in block:
                action[v] = value
        yield tuple(action)


def character(action, weights, moduli):
    return tuple(sum(weight * x[i] for x, weight in zip(action, weights)) % m
                 for i, m in enumerate(moduli))


def check_fibers():
    count = 0
    parts = list(partitions(list(range(4))))
    weights = [
        (0, 0, 0, 0), (1, -1, 2, -2), (3, -3, 6, -6),
        (4, 4, 4, -12), (2, 3, 5, -10), (6, 9, 12, -27),
    ]
    for high, low in [((9,), (3,)), ((4, 2), (2, 1)), ((4, 4), (2, 4))]:
        high_values = group(high)
        kernel = [x for x in high_values if reduce(x, low) == group(low)[0]]
        for upper in parts:
            upper_actions = list(axis_actions(upper, high))
            for lower in parts:
                if not all(any(set(block) <= set(target) for target in upper) for block in lower):
                    continue
                lower_actions = set(axis_actions(lower, low))
                for weight in weights:
                    g = gcd(lcm(*high), *(sum(weight[v] for v in block) for block in upper))
                    kernel_image = {reduce(tuple(g * t for t in k), high) for k in kernel}
                    upper_image = {reduce(tuple(g * t for t in x), high) for x in high_values}
                    lifts = {
                        action: Counter()
                        for action in lower_actions
                    }
                    for action in upper_actions:
                        reduction = tuple(reduce(x, low) for x in action)
                        lifts[reduction][character(action, weight, high)] += 1
                    counts = Counter()
                    for action, observed in lifts.items():
                        if any(len({action[v] for v in block}) != 1 for block in upper):
                            assert not observed
                            continue
                        # Use the representative of every reduced coordinate in the
                        # indicated interval as a lift to the corresponding upper factor.
                        translate = character(action, weight, high)
                        expected_targets = {
                            reduce(tuple(a + b for a, b in zip(translate, k)), high)
                            for k in kernel_image
                        }
                        fiber_size = len(kernel) ** (len(upper) - 1) // len(kernel_image)
                        assert observed == Counter({target: fiber_size for target in expected_targets})
                        counts.update(observed.keys())
                    survivors = prod(low) ** (len(upper) - 1) * len(kernel_image) // len(upper_image)
                    assert counts == Counter({target: survivors for target in upper_image})
                    count += 1
    return count


def check_collisions(p, n):
    original = range(1, p**n, p)
    checked = 0
    for j in range(1, n + 1):
        modulus = p**j
        for same_color in (False, True):
            records = [(x % modulus, same_color or x != 1) for x in original]
            for ratio in range(1, modulus, p):
                shifted = [(a * ratio % modulus, color) for a, color in records]
                assert (Counter(records) == Counter(shifted)) == (same_color or ratio == 1)
                checked += 1
    return checked


def profiles(n, prefix=()):
    if len(prefix) == n:
        yield prefix
        return
    for r in range(prefix[-1] if prefix else 0, len(prefix) + 1):
        yield from profiles(n, (*prefix, r))


def check_profiles(p, n):
    checked = 0
    for profile in profiles(n):
        pairs = [
            (p**h, index + 1)
            for index, h in enumerate(profile)
            if index == n - 1 or profile[index + 1] != h
        ]
        for j in range(1, n + 1):
            modulus = p**j
            units = range(1, modulus, p)
            components = [0]
            for weight, last in pairs:
                edge_scalar = pow(p, last, modulus)
                components.extend((weight, -weight) if edge_scalar == 0 else (0,))
            image = {1}
            for weight in components:
                powers = {pow(u, weight, modulus) for u in units}
                image = {a * b % modulus for a, b in product(image, powers)}
            assert (modulus - modulus // p) // len(image) == (p - 1) * p**profile[j - 1]
            checked += 1
    return checked



def check_cycles():
    # Bit 0 is the coefficient of x, bit 1 the coefficient of y.
    high_subgroups = ((0,), (0, 1), (0, 2), (0, 3), (0, 1, 2, 3))
    count = 0
    for side_groups in product(high_subgroups, repeat=3):
        for low_b, low_c in product(range(2), repeat=2):
            ratios = (low_b, low_b ^ low_c, low_c)
            choices = [tuple(g for g in subgroup if g % 2 == ratio)
                       for subgroup, ratio in zip(side_groups, ratios)]
            for b_weight, c_weight in product(range(2), repeat=2):
                observed = Counter()
                for b, c in product(range(4), repeat=2):
                    if (b % 2, c % 2) != (low_b, low_c):
                        continue
                    high_ratios = (b, b ^ c, c)
                    if all(g in subgroup for g, subgroup in zip(high_ratios, side_groups)):
                        observed[(b_weight * b) ^ (c_weight * c)] += 1
                expected = Counter()
                if all(choices):
                    a0, a1, a2 = (options[0] for options in choices)
                    residual = a0 ^ a1 ^ a2
                    base = (b_weight * a0) ^ (c_weight * (a0 ^ a1))
                    allowed = [tuple(g for g in subgroup if g % 2 == 0)
                               for subgroup in side_groups]
                    joint_image = Counter()
                    for k0, k1, k2 in product(*allowed):
                        cycle = k0 ^ k1 ^ k2
                        character = (b_weight * k0) ^ (c_weight * (k0 ^ k1))
                        joint_image[cycle, character] += 1
                    for (cycle, delta), fiber in joint_image.items():
                        if cycle == residual:
                            expected[base ^ delta] = fiber
                assert observed == expected
                count += 1
    return count


if __name__ == "__main__":
    print("character fibers", check_fibers())
    print("colliding label actions", check_collisions(3, 4) + check_collisions(5, 3))
    print("profile levels", check_profiles(3, 5) + check_profiles(5, 4))
    print("cycle and determinant fibers", check_cycles())
