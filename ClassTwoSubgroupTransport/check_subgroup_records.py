from itertools import product


def xor_all(values):
    answer = 0
    for value in values:
        answer ^= value
    return answer


def coordinates(basis):
    return {
        xor_all(basis[j] for j in range(len(basis)) if mask & (1 << j)): mask
        for mask in range(1 << len(basis))
    }


def value_at(mask, images):
    return xor_all(images[j] for j in range(len(images)) if mask & (1 << j))


class ElementaryQuotientGroup:
    def __init__(self, rank, center_rank, pairs):
        self.rank = rank
        self.center_rank = center_rank
        self.pairs = pairs

    def multiply(self, left, right):
        a, c = left
        b, d = right
        carry = xor_all(
            output for i, j, output in self.pairs if a & (1 << j) and b & (1 << i)
        )
        return a ^ b, c ^ d ^ carry

    def beta(self, left, right):
        return xor_all(
            (output if left & (1 << j) and right & (1 << i) else 0)
            ^ (output if right & (1 << j) and left & (1 << i) else 0)
            for i, j, output in self.pairs
        )

    def ordered_product(self, elements):
        output = (0, 0)
        for element in elements:
            output = self.multiply(output, element)
        return output


def central_shift_profiles(group, bases, reduce_center):
    return {
        tuple(reduce_center(value_at(a, images)) for basis in bases for a in basis)
        for images in product(range(1 << group.center_rank), repeat=group.rank)
    }


def relation_control(group, bases, kernel_basis):
    local_coords = [coordinates(basis) for basis in bases]
    assert all(len(coords) == 1 << len(basis) for coords, basis in zip(local_coords, bases))
    center_kernel = tuple(coordinates(kernel_basis))
    center_mod = lambda c: min(c ^ k for k in center_kernel)
    reduced_center = {center_mod(c) for c in range(1 << group.center_rank)}
    base_sections = [
        {
            vector: group.ordered_product(
                (a, 0) for j, a in enumerate(basis) if mask & (1 << j)
            )
            for vector, mask in coords.items()
        }
        for basis, coords in zip(bases, local_coords)
    ]
    for section in base_sections:
        for a, b in product(section, repeat=2):
            assert group.multiply(section[a], section[b])[0] == a ^ b
            lhs = group.multiply(section[a], section[b])[1]
            assert center_mod(lhs ^ section[a ^ b][1]) == 0

    relations = [rel for rel in product(*local_coords) if xor_all(rel) == 0]
    delta = {
        rel: center_mod(group.ordered_product(section[a] for section, a in zip(base_sections, rel))[1])
        for rel in relations
    }
    nonzero_polars = 0
    for left, right in product(relations, repeat=2):
        total = tuple(a ^ b for a, b in zip(left, right))
        polar = xor_all(
            group.beta(left[j], right[i]) for j in range(len(bases)) for i in range(j)
        )
        assert delta[total] ^ delta[left] ^ delta[right] == center_mod(polar)
        nonzero_polars += center_mod(polar) != 0

    global_profiles = central_shift_profiles(group, bases, center_mod)
    starts = [sum(len(basis) for basis in bases[:i]) for i in range(len(bases) + 1)]
    profile_count = 0
    for profile in product(sorted(reduced_center), repeat=starts[-1]):
        local_images = [profile[a:b] for a, b in zip(starts, starts[1:])]
        transformed = [
            {a: (a, c ^ value_at(coords[a], images)) for a, (_, c) in section.items()}
            for section, coords, images in zip(base_sections, local_coords, local_images)
        ]
        record_same = all(
            delta[rel]
            == center_mod(group.ordered_product(section[a] for section, a in zip(transformed, rel))[1])
            for rel in relations
        )
        assert record_same == (profile in global_profiles)
        profile_count += 1
    return len(relations), nonzero_polars, profile_count


def mixed_order_power_control():
    def multiply(left, right):
        i, j, k = left
        u, v, w = right
        return (i + u) % 8, (j + (-1) ** k * v) % 4, (k + w) % 2

    def fourth_power(x):
        square = multiply(x, x)
        return multiply(square, square)

    original = {(0, 0, 0), (4, 0, 0)}
    different = {(0, 0, 0), (4, 2, 0)}
    derived = {(0, 0, 0), (0, 2, 0)}
    assert {fourth_power(x) for x in product(range(8), range(4), range(2))} == original
    assert original & derived == different & derived == {(0, 0, 0)}
    assert {multiply(h, z) for h in original for z in derived} == {
        multiply(h, z) for h in different for z in derived
    }


def test_individually_compatible_marks():
    group = ElementaryQuotientGroup(4, 1, [(0, 1, 1)])
    profiles = central_shift_profiles(group, [(4,), (8,), (12,)], lambda c: c)
    expected = (0, 0, 1)
    assert expected not in profiles
    for i, j in [(0, 1), (0, 2), (1, 2)]:
        assert any(actual[i] == expected[i] and actual[j] == expected[j] for actual in profiles)


def triangular_group_control():
    group = ElementaryQuotientGroup(5, 2, [(0, 1, 1), (2, 3, 2)])
    kernels = [(0, 1), (0, 2), (0, 3)]
    local_shifts = (0, 0, 1)
    a = 16
    source = [{(0, k) for k in kernel} | {(a, k) for k in kernel} for kernel in kernels]
    target = [
        {(0, k) for k in kernel} | {(a, k ^ shift) for k in kernel}
        for kernel, shift in zip(kernels, local_shifts)
    ]
    for side in (source, target):
        for subgroup in side:
            assert len(subgroup) == 4
            assert all(group.multiply(x, y) in subgroup for x, y in product(subgroup, repeat=2))

    def matches(shift, i):
        shifted = {(q, c ^ (shift if q & a else 0)) for q, c in source[i]}
        return shifted == target[i]

    for i, j in [(0, 1), (0, 2), (1, 2)]:
        assert any(matches(shift, i) and matches(shift, j) for shift in range(4))
        assert {a ^ b for a in kernels[i] for b in kernels[j]} == set(range(4))
    assert not any(all(matches(shift, i) for i in range(3)) for shift in range(4))


def triple_profile_control():
    subspaces = ((0,), (0, 1), (0, 2), (0, 3), (0, 1, 2, 3))
    zero_function = (0, 0, 0, 0)
    local = {}
    reduced = {}
    for u, k in product(subspaces, repeat=2):
        center_mod = tuple(min(x ^ y for y in k) for x in range(4))
        reduced[k] = center_mod
        basis = {1: (), 2: (u[-1],), 4: (1, 2)}[len(u)]
        coords = coordinates(basis)
        values = sorted(set(center_mod))
        local[u, k] = []
        for images in product(values, repeat=len(basis)):
            function = list(zero_function)
            for a in u:
                function[a] = value_at(coords[a], images)
            local[u, k].append(tuple(function))

    shapes = 0
    profiles = 0
    pure_false_positives = 0
    for pairs in product(local, repeat=3):
        us = [u for u, _ in pairs]
        ks = [k for _, k in pairs]
        allowed_global = set()
        for images in product(range(4), repeat=2):
            global_profile = []
            for u, k in pairs:
                function = [reduced[k][value_at(a, images)] if a in u else 0 for a in range(4)]
                global_profile.append(tuple(function))
            allowed_global.add(tuple(global_profile))

        pair_checks = []
        for i, j in [(0, 1), (0, 2), (1, 2)]:
            sum_kernel = {a ^ b for a, b in product(ks[i], ks[j])}
            overlap = set(us[i]).intersection(us[j]) - {0}
            if len(sum_kernel) < 4 and overlap:
                pair_checks.append((i, j, sum_kernel, overlap))
        sum_all = {xor_all(values) for values in product(*ks)}
        triple_relations = []
        if len(sum_all) < 4:
            triple_relations = [(a, b, a ^ b) for a, b in product(us[0], us[1]) if (a ^ b) in us[2]]
        diagonal = {tuple(reduced[k][c] for k in ks) for c in range(4)}
        overlap = set(us[0]).intersection(us[1], us[2]) - {0}

        for profile in product(*(local[key] for key in pairs)):
            pure_equal = all(
                all((profile[i][a] ^ profile[j][a]) in kernel for a in common)
                for i, j, kernel, common in pair_checks
            ) and all(
                (profile[0][a] ^ profile[1][b] ^ profile[2][c]) in sum_all
                for a, b, c in triple_relations
            )
            overlap_equal = all(tuple(profile[i][a] for i in range(3)) in diagonal for a in overlap)
            feasible = profile in allowed_global
            assert (pure_equal and overlap_equal) == feasible
            pure_false_positives += pure_equal and not feasible
            profiles += 1
        shapes += 1
    assert pure_false_positives
    return shapes, profiles, pure_false_positives

def four_mark_rank_control():
    bases = ((1, 2), (4, 8), (5, 10), (9, 14))
    parity = lambda x: x.bit_count() & 1

    def outer(u, f):
        return xor_all(f << (4 * i) for i in range(4) if u & (1 << i))

    assert all(
        set(coordinates(bases[i])).intersection(coordinates(bases[j])) == {0}
        for i in range(4) for j in range(i)
    )
    columns = tuple(outer(u, f) for basis in bases for u, f in product(basis, repeat=2))
    full_tensor_kernel = [profile for profile in range(1 << 16) if value_at(profile, columns) == 0]
    assert len(full_tensor_kernel) == 4

    def slot_rank(profile, i):
        first_row = (profile >> (4 * i)) & 3
        second_row = (profile >> (4 * i + 2)) & 3
        return len({first_row, second_row} - {0})

    bounded_rank_one = [
        relation for relation in full_tensor_kernel
        if all(slot_rank(relation, i) <= 1 for i in range(4))
    ]
    bounded_rank_two = [
        relation for relation in full_tensor_kernel
        if all(slot_rank(relation, i) <= 2 for i in range(4))
    ]
    assert bounded_rank_one == [0] and bounded_rank_two == full_tensor_kernel

    global_profiles = set()
    for images in product(range(16), repeat=4):
        bits = [
            parity(value_at(u, images) & f) for basis in bases for u, f in product(basis, repeat=2)
        ]
        global_profiles.add(sum(bit << i for i, bit in enumerate(bits)))
    for profile in range(1 << 16):
        rank_two_pass = all(not parity(profile & relation) for relation in bounded_rank_two)
        assert rank_two_pass == (profile in global_profiles)
    assert 1 not in global_profiles

    group = ElementaryQuotientGroup(12, 4, [(2 * i, 2 * i + 1, 1 << i) for i in range(4)])
    kernels = [
        {c for c in range(16) if all(not parity(c & f) for f in basis)}
        for basis in bases
    ]
    assert all(
        {a ^ b for a, b in product(kernels[i], kernels[j])} == set(range(16))
        for i in range(4) for j in range(i)
    )
    for i, basis in enumerate(bases):
        coords = coordinates(basis)
        source = {(u << 8, c) for u in coords for c in kernels[i]}
        target = {
            (u << 8, c ^ (coords[u] & 1 if i == 0 else 0))
            for u in coords for c in kernels[i]
        }
        for subgroup in (source, target):
            assert len(subgroup) == 16
            assert all(group.multiply(x, y) in subgroup for x, y in product(subgroup, repeat=2))
    return len(bounded_rank_one), len(bounded_rank_two), len(global_profiles)

def main():
    mixed_order_power_control()
    test_individually_compatible_marks()
    triangular_group_control()
    one = ElementaryQuotientGroup(4, 1, [(0, 1, 1)])
    two = ElementaryQuotientGroup(4, 2, [(0, 1, 1), (2, 3, 2)])
    test_cases = [
        (one, [(4,), (8,), (12,)], ()),
        (one, [(1,), (2,), (1,), (2,)], ()),
        (two, [(1, 2), (1, 4), (2, 4)], (1,)),
        (two, [(5, 10), (1, 4), (2, 8)], (3,)),
        (two, [(1, 4), (2, 8), (9,), (6,)], ()),
    ]
    results = [relation_control(*case) for case in test_cases]
    assert any(polar_count > 0 for _, polar_count, _ in results)
    print("Mixed-order power and pairwise-compatibility controls passed.")
    print("Relation controls (relations, nonzero polars, lift profiles):", results)
    print("Triple controls (shapes, lift profiles, relation-only false positives):", triple_profile_control())
    print("Four-mark controls (rank-1 kernel, rank-2 kernel, possible lift profiles):", four_mark_rank_control())


if __name__ == "__main__":
    main()