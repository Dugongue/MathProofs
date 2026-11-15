"""Coordinate compiler for TensorOrderReduction.ordinary and smaller rank tags."""

from dataclasses import dataclass, replace
from functools import lru_cache
from itertools import accumulate, permutations, product
from math import prod

import numpy as np


Shape = tuple[int, int, int]


@dataclass(frozen=True)
class ProductNode:
    dimension: int
    modes: tuple[int, ...]
    children: tuple[int, int] | None


@dataclass(frozen=True)
class MixedSystem:
    input_shape: tuple[int, ...]
    nodes: tuple[ProductNode, ...]
    roots: Shape

    @property
    def grouped_shape(self) -> Shape:
        return tuple(self.nodes[node].dimension for node in self.roots)

    @property
    def products(self) -> tuple[int, ...]:
        return tuple(i for i, node in enumerate(self.nodes) if node.children is not None)


def make_system(shape, partition="balanced") -> MixedSystem:
    shape = tuple(int(n) for n in shape)
    order = len(shape)
    if order < 3 or any(n <= 0 for n in shape):
        raise ValueError("expected at least three positive dimensions")
    if partition == "balanced":
        sizes = (order // 3, (order + 1) // 3, (order + 2) // 3)
    elif partition == "half":
        sizes = (order // 2, order - order // 2 - 1, 1)
    else:
        sizes = tuple(partition)
        if len(sizes) != 3 or min(sizes) <= 0 or sum(sizes) != order:
            raise ValueError("partition must give three positive group sizes summing to the order")
    nodes = []
    mode = 0
    roots = []
    for size in sizes:
        prefix = len(nodes)
        nodes.append(ProductNode(shape[mode], (mode,), None))
        mode += 1
        for _ in range(1, size):
            leaf = len(nodes)
            nodes.append(ProductNode(shape[mode], (mode,), None))
            parent = len(nodes)
            node = nodes[prefix]
            nodes.append(ProductNode(node.dimension * shape[mode], node.modes + (mode,), (prefix, leaf)))
            prefix = parent
            mode += 1
        roots.append(prefix)
    return MixedSystem(shape, tuple(nodes), tuple(roots))


@dataclass(frozen=True)
class Run:
    origin: Shape
    step: Shape
    count: int

    def offset(self, axis, amount):
        point = list(self.origin)
        point[axis] += amount
        return replace(self, origin=tuple(point))

    def after(self, offset, count):
        return replace(
            self,
            origin=tuple(x + d * offset for x, d in zip(self.origin, self.step)),
            count=count,
        )


@dataclass(frozen=True)
class DenseBlock:
    origin: Shape
    data: np.ndarray
    step: Shape = (1, 1, 1)


@dataclass(frozen=True)
class CoordinateTensor:
    """Tensor with disjoint dense blocks and implicit unit-valued arithmetic runs."""

    shape: Shape
    runs: tuple[Run, ...]
    blocks: tuple[DenseBlock, ...]
    system: MixedSystem
    partitions: tuple[tuple[int, ...], ...] | None = None

    @property
    def nnz(self) -> int:
        return sum(run.count for run in self.runs) + sum(
            int(np.count_nonzero(block.data)) for block in self.blocks
        )

    def coo(self, max_nnz=2_000_000):
        if self.nnz > max_nnz or max(self.shape) > np.iinfo(np.int64).max:
            raise ValueError("tensor exceeds coordinate materialization limits")
        coordinates = []
        values = []
        for run in self.runs:
            points = np.arange(run.count, dtype=np.int64)
            coordinates.append(np.asarray(run.origin) + points[:, None] * np.asarray(run.step))
            values.append(np.ones(run.count, dtype=np.int64))
        for block in self.blocks:
            points = np.asarray(block.data.nonzero()).T
            coordinates.append(points * np.asarray(block.step) + np.asarray(block.origin))
            values.append(block.data[tuple(points.T)])
        return np.concatenate(coordinates), np.concatenate(values)

    def materialize(self, max_entries=10_000_000):
        if prod(self.shape) > max_entries or max(self.shape) > np.iinfo(np.intp).max:
            raise ValueError(f"dense tensor exceeds capacity, shape={self.shape}")
        matrix = np.zeros(self.shape, dtype=np.result_type(*(block.data.dtype for block in self.blocks), np.int64))
        for run in self.runs:
            points = np.arange(run.count, dtype=np.intp)
            matrix[tuple(x + d * points for x, d in zip(run.origin, run.step))] = 1
        for block in self.blocks:
            window = tuple(slice(x, x + d * n, d) for x, d, n in zip(block.origin, block.step, block.data.shape))
            matrix[window] = block.data
        return matrix


def _offsets(sizes):
    return tuple(accumulate(sizes, initial=0))


def _point(coordinates):
    return Run(tuple(coordinates), (0, 0, 0), 1)


def _pair(first, second, third, count, pair):
    return Run((first, second, third), tuple(int(i in pair) for i in range(3)), count)


def _pack(system, payload):
    """Basis evaluation of pack/encode/payload/coupling with ordered direct sums."""
    count = len(system.nodes)
    # (node, negative variance). Component order is immaterial if shared with occurrences.
    components = []
    for i in system.products:
        left, right = system.nodes[i].children
        components.append(((left, False), (right, False), (i, True)))
    components.append(tuple((i, False) for i in system.roots))
    names = [(i, dual) for i in range(count) for dual in (False, True)]
    occurrences = (
        [component[k] for k in range(3) for component in components]
        + [(i, False) for i in range(count)] + [(i, True) for i in range(count)]
    )
    named_index = {name: i for i, name in enumerate(names)}

    def dimension(name):
        return system.nodes[name[0]].dimension

    named_offsets = _offsets(dimension(name) for name in names)
    occur_offsets = _offsets(dimension(name) for name in occurrences)
    number_names, number_occurrences = len(names), len(occurrences)
    label_dim = number_names + number_occurrences + 1
    named_dim, occur_dim = named_offsets[-1], occur_offsets[-1]
    bases = (1, label_dim, named_dim, occur_dim)
    specs = (
        ((0, False), (1, False), (2, False), (3, False), (3, True)),
        ((0, True), (1, True), (3, False), (3, True)),
        ((0, True), (1, True), (2, True), (3, False), (3, True)),
    )
    (u0, u1, u2, u3, _), (v0, v1, v2, _), (w0, w1, w2, w3, w4) = (
        _offsets(bases[i] for i, _ in axis)[:-1] for axis in specs
    )
    sizes = tuple(sum(bases[i] for i, _ in axis) for axis in specs)
    runs = [
        _point((u0, v0, w0)),
        _pair(u1, v1 + 1, w0, label_dim - 1, (0, 1)),
        _point((u0, v1, w0)),
    ]
    for j, name in enumerate(names):
        runs.append(_pair(u2 + named_offsets[j], v1 + j, w2 + named_offsets[j], dimension(name), (0, 2)))
    for j, name in enumerate(occurrences):
        position = occur_offsets[j]
        label = v1 + number_names + j
        named_position = named_offsets[named_index[name]]
        runs.append(_pair(u3 + position, label, w4 + position, dimension(name), (0, 2)))
        runs.append(_pair(u3 + position, v0, w2 + named_position, dimension(name), (0, 2)))

    component_count = len(components)
    for j, node_index in enumerate(system.products):
        left, right = system.nodes[node_index].children
        left_dim = system.nodes[left].dimension
        right_dim = system.nodes[right].dimension
        u = u3 + occur_offsets[j]
        v = v2 + occur_offsets[component_count + j]
        w = w3 + occur_offsets[2 * component_count + j]
        if left_dim <= right_dim:
            runs.extend(
                Run((u + a, v, w + a * right_dim), (0, 1, 1), right_dim)
                for a in range(left_dim)
            )
        else:
            runs.extend(
                Run((u, v + b, w + b), (1, 0, right_dim), left_dim)
                for b in range(right_dim)
            )
    last = component_count - 1
    root_origin = (
        u3 + occur_offsets[last],
        v2 + occur_offsets[component_count + last],
        w3 + occur_offsets[2 * component_count + last],
    )
    for j, node in enumerate(system.nodes):
        first = u3 + occur_offsets[3 * component_count + count + j]
        second = v2 + occur_offsets[3 * component_count + j]
        third = w1 + named_index[(j, False)]
        runs.append(_pair(first, second, third, node.dimension, (0, 1)))
    return CoordinateTensor(sizes, tuple(runs), (DenseBlock(root_origin, payload),), system), specs, bases


def _linked(packed, specs, bases):
    """Basis evaluation of compile_apply and splitParts."""
    base_count = len(bases)
    mark_counts = (2 * base_count + len(specs[1]), base_count + len(specs[2]), 2 * base_count + len(specs[0]))
    parts = tuple(
        tuple(bases[i] for i, _ in spec) + bases + bases + (1,) * mark_count + (1,)
        for spec, mark_count in zip(specs, mark_counts)
    )
    offsets = tuple(_offsets(axis) for axis in parts)
    positive = tuple(tuple(offsets[k][len(specs[k]) + i] for i in range(base_count)) for k in range(3))
    negative = tuple(tuple(offsets[k][len(specs[k]) + base_count + i] for i in range(base_count)) for k in range(3))
    markers = tuple(offsets[k][len(specs[k]) + 2 * base_count] for k in range(3))
    anchors = tuple(axis[-2] for axis in offsets)
    runs = list(packed.runs)
    runs.append(_point(anchors))
    for axis, marker in enumerate(markers):
        point = list(anchors)
        point[axis] = marker
        stride = tuple(int(k == axis) for k in range(3))
        runs.append(Run(tuple(point), stride, mark_counts[axis]))
    for i, dimension in enumerate(bases):
        runs.extend((
            _pair(positive[0][i], negative[1][i], markers[2] + i, dimension, (0, 1)),
            _pair(positive[0][i], markers[1] + i, negative[2][i], dimension, (0, 2)),
            _pair(markers[0] + i, positive[1][i], negative[2][i], dimension, (1, 2)),
            _pair(markers[0] + base_count + i, negative[1][i], positive[2][i], dimension, (1, 2)),
            _pair(negative[0][i], positive[1][i], markers[2] + base_count + i, dimension, (0, 1)),
        ))
    for j, (i, is_dual) in enumerate(specs[0]):
        hub = positive if is_dual else negative
        runs.append(_pair(offsets[0][j], hub[1][i], markers[2] + 2 * base_count + j, bases[i], (0, 1)))
    for j, (i, is_dual) in enumerate(specs[1]):
        hub = positive if is_dual else negative
        runs.append(_pair(markers[0] + 2 * base_count + j, offsets[1][j], hub[2][i], bases[i], (1, 2)))
    for j, (i, is_dual) in enumerate(specs[2]):
        hub = positive if is_dual else negative
        runs.append(_pair(hub[0][i], markers[1] + base_count + j, offsets[2][j], bases[i], (0, 2)))
    return CoordinateTensor(
        tuple(axis[-1] for axis in offsets), tuple(runs), packed.blocks, packed.system, parts
    )


def _insert(runs, blocks, axis, cut, added):
    if added == 0:
        return runs, blocks
    new_runs = []
    for run in runs:
        origin, step = run.origin[axis], run.step[axis]
        if origin >= cut:
            new_runs.append(run.offset(axis, added))
        elif origin + (run.count - 1) * step < cut:
            new_runs.append(run)
        else:
            before = (cut - origin + step - 1) // step
            new_runs.append(run.after(0, before))
            new_runs.append(run.after(before, run.count - before).offset(axis, added))
    new_blocks = []
    for block in blocks:
        origin = block.origin[axis]
        size = block.data.shape[axis]
        step = block.step[axis]
        if origin + step * (size - 1) < cut:
            new_blocks.append(block)
        elif origin >= cut:
            new_origin = list(block.origin)
            new_origin[axis] += added
            new_blocks.append(replace(block, origin=tuple(new_origin)))
        else:
            split = (cut - origin + step - 1) // step
            before = [slice(None)] * 3
            after = [slice(None)] * 3
            before[axis] = slice(0, split)
            after[axis] = slice(split, None)
            start = list(block.origin)
            start[axis] = origin + step * split + added
            new_blocks.append(replace(block, data=block.data[tuple(before)]))
            new_blocks.append(DenseBlock(tuple(start), block.data[tuple(after)], block.step))
    return tuple(new_runs), tuple(new_blocks)


def _delete_row(tensor, tag_policy):
    """Execute deleteRow with one implicit diagonal run for each new identity."""
    front_parts, column_parts, row_parts = tensor.partitions
    front, column, row = tensor.shape
    number = len(row_parts)
    first_front, first_column = front_parts[0], column_parts[0]
    if tag_policy == "geometric":
        tags = tuple((1 << i) * (row + 1) for i in range(number))
    elif tag_policy == "compact":
        base = max(number, max(row_parts) + 1)
        tags = tuple(base + i - dim for i, dim in enumerate(row_parts))
    else:
        raise ValueError("unknown tag policy")
    row_offsets = _offsets(row_parts)
    tag_offsets = _offsets(tags)
    column_extra = row + tag_offsets[-1]
    runs, blocks = _insert(tensor.runs, tensor.blocks, 0, first_front, number)
    runs, blocks = _insert(runs, blocks, 1, first_column, column_extra)
    new_runs = list(runs)
    for i, (dim, tag) in enumerate(zip(row_parts, tags)):
        # Original columns copy into the ith independent row block.
        left = first_front + i
        copies = row + i * column
        new_runs.append(_pair(left, 0, copies, first_column, (1, 2)))
        if first_column < column:
            new_runs.append(_pair(left, first_column + column_extra, copies + first_column, column - first_column, (1, 2)))
        # The ith original row block is paired with its auxiliary column.
        new_runs.append(_pair(left, first_column + row_offsets[i], row_offsets[i], dim, (1, 2)))
        # The large tag space requires only this run descriptor.
        new_runs.append(_pair(
            left, first_column + row + tag_offsets[i], row + number * column + tag_offsets[i], tag, (1, 2)
        ))
    new_row = row + number * column + tag_offsets[-1]
    return CoordinateTensor(
        (front + number, column + column_extra, new_row),
        tuple(new_runs),
        blocks,
        tensor.system,
        ((first_front + number,) + front_parts[1:], (first_column + column_extra,) + column_parts[1:], (new_row,)),
    )


def _permute(tensor, permutation):
    if permutation == (0, 1, 2):
        return tensor

    def reorder(axis):
        return tuple(axis[i] for i in permutation)

    return CoordinateTensor(
        reorder(tensor.shape),
        tuple(Run(reorder(run.origin), reorder(run.step), run.count) for run in tensor.runs),
        tuple(DenseBlock(reorder(block.origin), block.data.transpose(permutation), reorder(block.step)) for block in tensor.blocks),
        tensor.system,
        reorder(tensor.partitions),
    )


def _mod_poly(value, divisor):
    while value.bit_length() >= divisor.bit_length():
        value ^= divisor << (value.bit_length() - divisor.bit_length())
    return value


@lru_cache(maxsize=64)
def _irreducibles(number):
    degree = 1
    while True:
        divisors = [
            polynomial
            for d in range(1, degree // 2 + 1)
            for polynomial in range((1 << d) | 1, 1 << (d + 1), 2)
        ]
        good = []
        for polynomial in range((1 << degree) | 1, 1 << (degree + 1), 2):
            if all(_mod_poly(polynomial, divisor) for divisor in divisors):
                good.append(polynomial)
                if len(good) == number:
                    return degree, tuple(good)
        degree += 1


def _binary_rank(columns):
    pivots = {}
    for value in columns:
        while value:
            bit = value.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = value
                break
            value ^= pivots[bit]
    return len(pivots)


@lru_cache(maxsize=128)
def _spectral_data(row_parts):
    degree, polynomials = _irreducibles(len(row_parts))
    operators = tuple(
        (
            tuple(1 << i for i in range(degree)),
            tuple(_mod_poly(1 << (i + 1), polynomial) for i in range(degree)),
            tuple(_mod_poly(1 << (2 * i), polynomial) for i in range(degree)),
        )
        for polynomial in polynomials
    )
    supports = ((0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2))
    ranks = []
    for support in supports:
        value = 0
        for dim, marker in zip(row_parts, operators):
            columns = [0] * degree
            for i in support:
                for j, bits in enumerate(marker[i]):
                    columns[j] ^= bits
            value += dim * _binary_rank(columns)
        ranks.append(value)
    for tags in product(range(1, 20), repeat=3):
        if len(set(tags)) != 3:
            continue
        singleton = {ranks[i] + tags[i] for i in range(3)}
        if all(rank + sum(tags[i] for i in support) not in singleton for rank, support in zip(ranks[3:], supports[3:])):
            return degree, operators, tags, tuple(ranks)
    raise AssertionError("no rank tags found, contrary to the counting bound")


def _delete_binary_spectral(tensor, _tag_policy):
    """Proof-adapted binary-field erasure using three marked matrix operators."""
    front_parts, column_parts, row_parts = tensor.partitions
    front, column, row = tensor.shape
    degree, operators, tags, _ = _spectral_data(row_parts)
    first_front, first_column = front_parts[0], column_parts[0]
    row_offsets = _offsets(degree * dim for dim in row_parts)
    tag_offsets = _offsets(tags)
    expanded_row = degree * row
    column_extra = expanded_row + tag_offsets[-1]
    runs, blocks = _insert(tensor.runs, tensor.blocks, 0, first_front, 3)
    runs, blocks = _insert(runs, blocks, 1, first_column, column_extra)

    def expand(axis):
        return (axis[0], axis[1], degree * axis[2])

    new_runs = [Run(expand(run.origin), expand(run.step), run.count) for run in runs]
    new_blocks = [DenseBlock(expand(block.origin), block.data, expand(block.step)) for block in blocks]
    for marker in range(3):
        on_front = first_front + marker
        copy = expanded_row + marker * column
        new_runs.append(_pair(on_front, 0, copy, first_column, (1, 2)))
        if first_column < column:
            new_runs.append(_pair(on_front, first_column + column_extra, copy + first_column, column - first_column, (1, 2)))
        tag_column = first_column + expanded_row + tag_offsets[marker]
        tag_row = expanded_row + 3 * column + tag_offsets[marker]
        new_runs.append(_pair(on_front, tag_column, tag_row, tags[marker], (1, 2)))
        for i, dim in enumerate(row_parts):
            for input_coord, output_bits in enumerate(operators[i][marker]):
                for output_coord in range(degree):
                    if (output_bits >> output_coord) & 1:
                        new_runs.append(Run((
                            on_front,
                            first_column + row_offsets[i] + input_coord,
                            row_offsets[i] + output_coord,
                        ), (0, degree, degree), dim))
    new_row = expanded_row + 3 * column + tag_offsets[-1]
    return CoordinateTensor(
        (front + 3, column + column_extra, new_row),
        tuple(new_runs),
        tuple(new_blocks),
        tensor.system,
        ((first_front + 3,) + front_parts[1:], (first_column + column_extra,) + column_parts[1:], (new_row,)),
    )


def _part_shape_after_delete(parts, policy):
    front, column, row = parts
    rows = sum(row)
    cols = sum(column)
    if policy == "binary_spectral":
        degree, _, tags, _ = _spectral_data(row)
        count = 3
        rows *= degree
        tag_total = sum(tags)
    else:
        count = len(row)
        if policy == "compact":
            base = max(count, max(row) + 1)
            tag_total = count * base + count * (count - 1) // 2 - rows
        else:
            tag_total = ((1 << count) - 1) * (rows + 1)
    return ((front[0] + count,) + front[1:], (column[0] + rows + tag_total,) + column[1:], (rows + count * cols + tag_total,))


@lru_cache(maxsize=256)
def _best_schedule(partitions, policy):
    """Minimize the exact output volume over valid erasure orders."""
    def plans(parts, previous):
        if len(previous) == 3:
            return [(prod(sum(axis) for axis in parts), previous)]
        result = []
        for perm in permutations(range(3)):
            permuted = tuple(parts[i] for i in perm)
            if len(permuted[2]) > 1:
                result.extend(plans(_part_shape_after_delete(permuted, policy), previous + (perm,)))
        return result

    return min(plans(partitions, ()))[1]

def compile_tensor(tensor, partition="balanced", layer="ordinary", *, tag_policy="geometric", schedule="cyclic"):
    """Compile an ordered NumPy tensor without expanding rank-tag diagonals.

    Use the mixed stage for the named constrained three-way system, packed/linked
    for optional intermediate coordinates, and ordinary for the full reduction.
    The geometric policy matches Lean's tags up to a consistent choice of bases.
    Compact replaces them by arithmetically spaced singleton-recognizing weights.
    Binary spectral uses three rigid commuting tests on field-expanded row blocks.
    The minimum-entry schedule searches axis permutations with exact size arithmetic.
    """
    tensor = np.asarray(tensor)
    system = make_system(tensor.shape, partition)
    grouped = tensor.reshape(system.grouped_shape)
    if layer == "mixed":
        return CoordinateTensor(system.grouped_shape, (), (DenseBlock((0, 0, 0), grouped),), system)
    packed, specs, bases = _pack(system, grouped)
    if layer == "packed":
        return packed
    linked = _linked(packed, specs, bases)
    if layer == "linked":
        return linked
    if layer != "ordinary":
        raise ValueError("unknown layer")
    if tag_policy not in ("geometric", "compact", "binary_spectral"):
        raise ValueError("unknown tag policy")
    if tag_policy == "binary_spectral" and not np.all((tensor == 0) | (tensor == 1)):
        raise ValueError("binary spectral encoding requires coefficients 0 or 1 over F2")
    delete = _delete_binary_spectral if tag_policy == "binary_spectral" else _delete_row
    if schedule == "min_entries":
        plan = _best_schedule(linked.partitions, tag_policy)
    elif schedule == "cyclic":
        plan = ((0, 1, 2), (1, 2, 0), (1, 2, 0))
    else:
        raise ValueError("unknown erasure schedule")
    result = linked
    for permutation in plan:
        result = delete(_permute(result, permutation), tag_policy)
    return result


@dataclass(frozen=True)
class PathBlock:
    """Consecutive paths along one of the two arms in the published quiver."""

    source: int
    target: int
    offset: int
    width: int


def compile_published(tensor):
    """Grochow-Qiao's Fig. 6 quotient path algebra, as a bare multiplication tensor.

    The quotient construction is described in SIAM J. Comput. 52(2), §7.
    Order three is already in the target format and is passed through.
    Bare multiplication tensor isotopy is equivalent to unital associative
    algebra isomorphism. This implementation is independent of the rank tags.
    """
    tensor = np.asarray(tensor)
    shape = tensor.shape
    order = len(shape)
    if order < 3 or any(n <= 0 for n in shape):
        raise ValueError("expected at least three positive dimensions")
    if order == 3:
        return compile_tensor(tensor, layer="mixed")
    cut = order // 2 + 1
    arms = (shape[:cut], shape[cut:])
    sink = order - 1
    vertices = (
        (0, *range(1, cut), sink),
        (0, *range(cut, sink), sink),
    )
    paths = []
    next_coordinate = order
    for arm, dims in enumerate(arms):
        by_interval = {}
        for i in range(len(dims)):
            width = 1
            for j in range(i + 1, len(dims) + 1):
                width *= dims[j - 1]
                if arm == 0 and i == 0 and j == len(dims):
                    continue
                by_interval[i, j] = PathBlock(vertices[arm][i], vertices[arm][j], next_coordinate, width)
                next_coordinate += width
        paths.append(by_interval)
    runs = [_point((i, i, i)) for i in range(order)]
    blocks = []
    for arm, dims in enumerate(arms):
        by_interval = paths[arm]
        for (i, j), path in by_interval.items():
            runs.append(_pair(path.source, path.offset, path.offset, path.width, (1, 2)))
            runs.append(_pair(path.offset, path.target, path.offset, path.width, (0, 2)))
            for k in range(j + 1, len(dims) + 1):
                other = by_interval[j, k]
                joined = by_interval.get((i, k))
                if joined is None:
                    target = paths[1][0, len(arms[1])]
                    blocks.append(DenseBlock(
                        (path.offset, other.offset, target.offset),
                        tensor.reshape(path.width, other.width, target.width),
                    ))
                    continue
                if path.width <= other.width:
                    runs.extend(
                        Run((path.offset + a, other.offset, joined.offset + a * other.width), (0, 1, 1), other.width)
                        for a in range(path.width)
                    )
                else:
                    runs.extend(
                        Run((path.offset, other.offset + b, joined.offset + b), (1, 0, other.width), path.width)
                        for b in range(other.width)
                    )
    system = make_system(shape, "half")
    return CoordinateTensor((next_coordinate,) * 3, tuple(runs), tuple(blocks), system)
