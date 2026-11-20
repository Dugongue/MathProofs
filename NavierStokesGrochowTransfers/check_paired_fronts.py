"""Differential controls for paired fronts on binary lists of factor-center lines."""

from collections import Counter
from itertools import permutations, product
import json
from random import Random


def xor(values):
    total = 0
    for value in values:
        total ^= value
    return total


def members(mask, size):
    return [i for i in range(size) if mask >> i & 1]


def span(columns, mask):
    space = {0}
    for i in members(mask, len(columns)):
        space |= {value ^ columns[i] for value in space}
    return space


def submasks(mask):
    part = mask
    while True:
        yield part
        if part == 0:
            return
        part = (part - 1) & mask


def tree_split(mask):
    indices = members(mask, mask.bit_length())
    left = sum(1 << i for i in indices[: len(indices) // 2])
    return left, mask ^ left


def multiplicity(source, target, i, j):
    if source[i] == 0 and target[j] != 0:
        return 0
    # Distinct local maps with the same central restrictions must all count.
    return 1 + (3 * i + 2 * j) % 4


def brute_force(source, target):
    total = 0
    for assignment in permutations(range(len(source)), len(target)):
        images = [0] * len(source)
        weight = 1
        for j, i in enumerate(assignment):
            weight *= multiplicity(source, target, i, j)
            images[i] = target[j]
        prescribed = {}
        for choices in product(range(2), repeat=len(source)):
            x = xor(c for c, chosen in zip(source, choices) if chosen)
            y = xor(c for c, chosen in zip(images, choices) if chosen)
            if prescribed.setdefault(x, y) != y:
                break
        else:
            total += weight
    return total


class FrontControl:
    def __init__(self, source, target):
        self.source = source
        self.target = target
        self.n = len(source)
        self.m = len(target)
        self.all_source = (1 << self.n) - 1
        self.all_target = (1 << self.m) - 1
        self.relations = [
            mask for mask in range(self.all_source + 1)
            if xor(source[i] for i in members(mask, self.n)) == 0
        ]
        self.source_front = [
            [xor(source[i] for i in members(r & mask, self.n)) for r in self.relations]
            for mask in range(self.all_source + 1)
        ]
        self.target_cut = [
            span(target, mask) & span(target, self.all_target ^ mask)
            for mask in range(self.all_target + 1)
        ]
        self.zero = (0,) * len(self.relations)
        self.delta = (
            len(span(source, self.all_source)).bit_length()
            - len(span(target, self.all_target)).bit_length()
        )
        self.source_cut_dims = [
            len(set(values)).bit_length() - 1 for values in self.source_front
        ]
        self.target_cut_dims = [len(values).bit_length() - 1 for values in self.target_cut]

    def eligible(self, i_set, j_set):
        return abs(self.source_cut_dims[i_set] - self.target_cut_dims[j_set]) <= self.delta

    def valid(self, i_set, j_set, values):
        by_cut_value = {}
        for x, y in zip(self.source_front[i_set], values):
            if y not in self.target_cut[j_set] or by_cut_value.setdefault(x, y) != y:
                return False
        return True

    def match(self, i, j):
        weight = multiplicity(self.source, self.target, i, j)
        values = tuple(self.target[j] if r >> i & 1 else 0 for r in self.relations)
        if weight and self.valid(1 << i, 1 << j, values):
            return Counter({values: weight})
        return Counter()

    def combine(self, out, left, right, i_set, j_set):
        for a, multiplicity_a in left.items():
            for b, multiplicity_b in right.items():
                values = tuple(x ^ y for x, y in zip(a, b))
                if self.valid(i_set, j_set, values):
                    out[values] += multiplicity_a * multiplicity_b

    def source_tree(self, i_set, j_set):
        if not self.eligible(i_set, j_set):
            return Counter()
        if i_set.bit_count() <= 1:
            if not j_set:
                return Counter({self.zero: 1})
            if i_set and j_set.bit_count() == 1:
                return self.match(i_set.bit_length() - 1, j_set.bit_length() - 1)
            return Counter()
        left_i, right_i = tree_split(i_set)
        out = Counter()
        for left_j in submasks(j_set):
            right_j = j_set ^ left_j
            left = self.source_tree(left_i, left_j)
            right = self.source_tree(right_i, right_j)
            self.combine(out, left, right, i_set, j_set)
        return out

    def target_tree(self, i_set, j_set):
        if i_set.bit_count() != j_set.bit_count() or not self.eligible(i_set, j_set):
            return Counter()
        if j_set.bit_count() == 1:
            return self.match(i_set.bit_length() - 1, j_set.bit_length() - 1)
        left_j, right_j = tree_split(j_set)
        out = Counter()
        for left_i in submasks(i_set):
            right_i = i_set ^ left_i
            left = self.target_tree(left_i, left_j)
            right = self.target_tree(right_i, right_j)
            self.combine(out, left, right, i_set, j_set)
        return out

    def count_source_tree(self):
        return self.source_tree(self.all_source, self.all_target)[self.zero]

    def count_target_tree(self):
        if not self.m:
            return 1
        return sum(
            self.target_tree(i_set, self.all_target)[self.zero]
            for i_set in range(self.all_source + 1)
        )


def cases():
    for n in range(4):
        for m in range(4):
            for source in product(range(2), repeat=n):
                for target in product(range(2), repeat=m):
                    yield source, target
    rng = Random(5112026)
    for _ in range(400):
        n = rng.randrange(7)
        m = rng.randrange(7)
        source = tuple(rng.randrange(8) for _ in range(n))
        target = tuple(rng.randrange(8) for _ in range(m))
        yield source, target
        # Force a solution by taking a linear map annihilating omitted factors.
        retained = rng.sample(range(n), rng.randrange(n + 1))
        killed = [i for i in range(n) if i not in retained]
        annihilators = [
            u for u in range(8)
            if all((u & source[i]).bit_count() % 2 == 0 for i in killed)
        ]
        rows = rng.choices(annihilators, k=3)
        target = tuple(sum(((row & source[i]).bit_count() % 2) << j
                           for j, row in enumerate(rows)) for i in retained)
        yield source, target


def main():
    result = Counter()
    for source, target in cases():
        count = brute_force(source, target)
        solver = FrontControl(source, target)
        by_source = solver.count_source_tree()
        by_target = solver.count_target_tree()
        assert count == by_source == by_target, (source, target, count, by_source, by_target)
        result['cases'] += 1
        result['positive' if count else 'zero'] += 1
    result['dimension_drop_pruning'] = True
    print(json.dumps(result))


if __name__ == '__main__':
    main()
