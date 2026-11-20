"""Finite controls for GP030 and GP049 using explicit and product groups."""

from dataclasses import dataclass
from itertools import permutations


@dataclass(frozen=True)
class Group:
    size: int
    multiply: object
    inverse: object

    @property
    def elements(self):
        return range(self.size)


def permutation_group(degree, even_only=False):
    def even(permutation):
        inversions = sum(permutation[i] > permutation[j]
                         for i in range(degree) for j in range(i + 1, degree))
        return inversions % 2 == 0

    elements = list(permutations(range(degree)))
    if even_only:
        elements = [element for element in elements if even(element)]
    labels = {element: i for i, element in enumerate(elements)}
    table = [
        [labels[tuple(first[second[i]] for i in range(degree))] for second in elements]
        for first in elements
    ]
    inverses = [row.index(0) for row in table]
    return Group(len(elements), lambda a, b: table[a][b], inverses.__getitem__)


def cyclic(size):
    return Group(size, lambda a, b: (a + b) % size, lambda a: -a % size)


def direct_product(first, second):
    width = second.size

    def multiply(a, b):
        ai, aj = divmod(a, width)
        bi, bj = divmod(b, width)
        return width * first.multiply(ai, bi) + second.multiply(aj, bj)

    def inverse(a):
        ai, aj = divmod(a, width)
        return width * first.inverse(ai) + second.inverse(aj)

    return Group(first.size * width, multiply, inverse)


def subgroup_generated(group, candidates):
    generators = []
    seen = {0}
    for candidate in candidates:
        if candidate in seen:
            continue
        generators.append(candidate)
        frontier = list(seen)
        for a in frontier:
            for generator in generators:
                b = group.multiply(a, generator)
                if b not in seen:
                    seen.add(b)
                    frontier.append(b)
    return frozenset(seen)


def conjugates(group, x):
    return frozenset(group.multiply(group.multiply(g, x), group.inverse(g))
                     for g in group.elements)


def conjugacy_classes(group):
    unused = set(group.elements)
    while unused:
        x = min(unused)
        members = conjugates(group, x)
        yield x, members
        unused.difference_update(members)


def product(group, first, second):
    if len(first) == 1:
        return second
    if len(second) == 1:
        return first
    return frozenset(group.multiply(a, b) for a in first for b in second)


def normal_subgroups_independent(group):
    closures = {
        subgroup_generated(group, members)
        for _, members in conjugacy_classes(group)
    }
    normals = {frozenset((0,))}
    for closure in sorted(closures, key=len, reverse=True):
        normals |= {product(group, known, closure) for known in normals}
    return normals


def abelian(group, subgroup):
    return all(group.multiply(x, y) == group.multiply(y, x)
               for x in subgroup for y in subgroup)


def minimal_members(normals):
    proper = [subgroup for subgroup in normals if len(subgroup) > 1]
    return {subgroup for subgroup in proper
            if all(not other < subgroup for other in proper)}


def derived(group, subgroup):
    commutators = (
        group.multiply(group.multiply(group.inverse(a), group.inverse(b)),
                       group.multiply(a, b))
        for a in subgroup for b in subgroup
    )
    return subgroup_generated(group, commutators)


def solvable(group, subgroup):
    while len(subgroup) > 1:
        smaller = derived(group, subgroup)
        if smaller == subgroup:
            return False
        subgroup = smaller
    return True


def radical_independent(group):
    normals = normal_subgroups_independent(group)
    return max((normal for normal in normals if solvable(group, normal)), key=len)


def subgroup_model(group, subgroup):
    elements = sorted(subgroup)
    labels = {element: i for i, element in enumerate(elements)}
    return Group(
        len(elements),
        lambda a, b: labels[group.multiply(elements[a], elements[b])],
        lambda a: labels[group.inverse(elements[a])],
    ), elements


def quotient(group, normal):
    classes = []
    label = {}
    for representative in group.elements:
        if representative in label:
            continue
        i = len(classes)
        coset = frozenset(group.multiply(representative, h) for h in normal)
        classes.append(coset)
        for element in coset:
            label[element] = i
    representatives = tuple(min(coset) for coset in classes)
    model = Group(
        len(classes),
        lambda a, b: label[group.multiply(representatives[a], representatives[b])],
        lambda a: label[group.inverse(representatives[a])],
    )
    return model, classes


def bounded_masks(group, exponent):
    masks = {}
    for x, members in conjugacy_classes(group):
        powers = {0}
        z = x
        while z != 0:
            powers.add(z)
            z = group.multiply(z, x)
        seed = frozenset(
            group.multiply(group.multiply(g, z), group.inverse(g))
            for g in group.elements for z in powers
        )
        mask = seed
        for _ in range(exponent):
            if len(mask) == group.size:
                break
            step = product(group, mask, mask)
            if step == mask:
                break
            mask = step
        for element in members:
            masks[element] = mask
    return masks


def circuit_outputs(group):
    exponent = (8 * max(1, group.size.bit_length())).bit_length()
    masks = bounded_masks(group, exponent)
    found = set()
    for x, mask in masks.items():
        if x == 0 or mask in found:
            continue
        if all(masks[y] == mask for y in mask if y != 0) and product(group, mask, mask) == mask:
            found.add(mask)
    socle = frozenset({0})
    for normal in found:
        socle = product(group, socle, normal)
    simple = group.size > 1 and all(len(mask) == group.size for x, mask in masks.items() if x)
    return found, socle, simple


def fitting_free_kernels(group):
    radical = radical_independent(group)
    if len(radical) > 1:
        quotient_group, cosets = quotient(group, radical)
        return {
            frozenset(element for label in kernel for element in cosets[label])
            for kernel in fitting_free_kernels(quotient_group)
        }
    if group.size == 1:
        return {frozenset({0})}
    _, socle, _ = circuit_outputs(group)
    socle_group, labels = subgroup_model(group, socle)
    factors = [
        frozenset(labels[x] for x in normal)
        for normal in minimal_members(normal_subgroups_independent(socle_group))
    ]
    result = set()
    for keep in range(1 << len(factors)):
        retained = frozenset({0})
        discarded = frozenset({0})
        for i, factor in enumerate(factors):
            if keep >> i & 1:
                retained = product(group, retained, factor)
            else:
                discarded = product(group, discarded, factor)
        if any(conjugates(group, x) - retained for x in retained):
            continue
        centralizer = frozenset(x for x in group.elements
                                if all(group.multiply(x, y) == group.multiply(y, x)
                                       for y in retained))
        centralizer_group, elements = subgroup_model(group, centralizer)
        discarded_labels = frozenset(i for i, x in enumerate(elements) if x in discarded)
        smaller, cosets = quotient(centralizer_group, discarded_labels)
        for smaller_kernel in fitting_free_kernels(smaller):
            kernel = frozenset(elements[x] for label in smaller_kernel for x in cosets[label])
            if any(conjugates(group, x) - kernel for x in kernel):
                continue
            target, _ = quotient(group, kernel)
            if any(abelian(target, minimal) for minimal in circuit_outputs(target)[0]):
                continue
            assert kernel not in result
            result.add(kernel)
    return result


def chief_action_kernels(group):
    lower = frozenset({0})
    kernels = []
    while len(lower) < group.size:
        remainder, cosets = quotient(group, lower)
        minimals, _, _ = circuit_outputs(remainder)
        factor = min(minimals, key=lambda normal: min(normal - {0}))
        upper = frozenset(x for label in factor for x in cosets[label])
        if not abelian(remainder, factor):
            def commutator(a, b):
                conjugate = group.multiply(group.multiply(a, b), group.inverse(a))
                return group.multiply(conjugate, group.inverse(b))

            kernels.append(frozenset(
                a for a in group.elements
                if all(commutator(a, b) in lower for b in upper)
            ))
        lower = upper
    return kernels


def fitting_free_kernels_chief(group, remove_radical):
    if remove_radical:
        radical = radical_independent(group)
        if len(radical) > 1:
            smaller, cosets = quotient(group, radical)
            return {
                frozenset(x for label in kernel for x in cosets[label])
                for kernel in fitting_free_kernels_chief(smaller, remove_radical=False)
            }

    candidates = {frozenset(group.elements)}
    for kernel in chief_action_kernels(group):
        candidates |= {candidate & kernel for candidate in candidates}
    found = set()
    for candidate in candidates:
        target, _ = quotient(group, candidate)
        if all(not abelian(target, minimal) for minimal in circuit_outputs(target)[0]):
            found.add(candidate)
    return found

cases = [
    ("trivial", cyclic(1)),
    ("C7", cyclic(7)),
    ("C12", cyclic(12)),
    ("C2 x C2", direct_product(cyclic(2), cyclic(2))),
    ("S3", permutation_group(3)),
    ("S4", permutation_group(4)),
    ("A5", permutation_group(5, even_only=True)),
    ("S5", permutation_group(5)),
    ("A5 x C2", direct_product(permutation_group(5, even_only=True), cyclic(2))),
    ("S5 x C2", direct_product(permutation_group(5), cyclic(2))),
]
for name, group in cases:
    independent = normal_subgroups_independent(group)
    circuit_minimal, circuit_socle, circuit_simple = circuit_outputs(group)
    expected_minimal = minimal_members(independent)
    expected_socle = subgroup_generated(group, (x for normal in expected_minimal for x in normal))
    assert circuit_minimal == expected_minimal
    assert circuit_socle == expected_socle
    assert circuit_simple == (group.size > 1 and len(independent) == 2)
    expected_kernels = set()
    for kernel in independent:
        target, _ = quotient(group, kernel)
        if len(radical_independent(target)) == 1:
            expected_kernels.add(kernel)
    assert fitting_free_kernels(group) == expected_kernels
    assert fitting_free_kernels_chief(group, remove_radical=True) == expected_kernels
    assert fitting_free_kernels_chief(group, remove_radical=False) == expected_kernels
    print(name, "order", group.size, "minimals", len(circuit_minimal),
          "socle", len(circuit_socle), "Fitting-free kernels", len(expected_kernels))
