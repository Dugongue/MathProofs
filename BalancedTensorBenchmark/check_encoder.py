"""Exact finite checks for the coordinate compilers."""

import itertools
import math

import numpy as np

from encoder import (
    CoordinateTensor, DenseBlock, _binary_rank, _delete_binary_spectral, _delete_row,
    _spectral_data, compile_published, compile_tensor, make_system,
)


def expanded_reference(data, parts, policy):
    """Simple element-by-element expansion independent of run manipulation."""
    a_parts, b_parts, c_parts = parts
    a_size, b_size, c_size = data.shape
    count = len(c_parts)
    if policy == "geometric":
        tags = [(2**i) * (c_size + 1) for i in range(count)]
    else:
        base = max(count, max(c_parts) + 1)
        tags = [base + i - c_parts[i] for i in range(count)]
    extra = c_size + sum(tags)
    out = np.zeros((a_size + count, b_size + extra, c_size + count * b_size + sum(tags)), dtype=int)
    for a, b, c in np.ndindex(data.shape):
        ia = a if a < a_parts[0] else a + count
        ib = b if b < b_parts[0] else b + extra
        out[ia, ib, c] = data[a, b, c]
    for i in range(count):
        a_mark = a_parts[0] + i
        for b in range(b_size):
            ib = b if b < b_parts[0] else b + extra
            out[a_mark, ib, c_size + i * b_size + b] = 1
        for c in range(sum(c_parts[:i]), sum(c_parts[:i + 1])):
            out[a_mark, b_parts[0] + c, c] = 1
        for tag in range(sum(tags[:i]), sum(tags[:i + 1])):
            out[a_mark, b_parts[0] + c_size + tag, c_size + count * b_size + tag] = 1
    return out


def check_delete_row(rng):
    total = 0
    for parts in [((1, 2), (1, 1), (1, 1)), ((3,), (2, 1), (1, 2)), ((2, 1), (3,), (1, 2, 1))]:
        shape = tuple(map(sum, parts))
        for policy in ("geometric", "compact"):
            for q in (2, 3, 5):
                data = rng.integers(0, q, size=shape)
                case = CoordinateTensor(
                    shape, (), (DenseBlock((0, 0, 0), data),), make_system(shape), parts
                )
                encoded = _delete_row(case, policy)
                dense = encoded.materialize()
                assert np.array_equal(dense, expanded_reference(data, parts, policy))
                assert encoded.nnz == np.count_nonzero(dense)
                total += 1
    return total


def check_published(rng):
    """Verify unit and associativity by basis multiplication in small fields."""
    total = 0
    for order, shape in [(4, (2, 2, 2, 2)), (5, (2, 1, 2, 1, 2)), (6, (2,) * 6)]:
        for q in (2, 3, 5):
            array = rng.integers(0, q, size=shape)
            encoded = compile_published(array)
            dense = encoded.materialize()
            side = encoded.shape[0]
            identity = np.eye(side, dtype=int)
            assert np.array_equal(dense[:order].sum(axis=0), identity)
            assert np.array_equal(dense[:, :order].sum(axis=1), identity)
            assert encoded.nnz == np.count_nonzero(dense)
            for i, j, k in rng.integers(0, side, size=(125, 3)):
                left = dense[i, j, :] @ dense[:, k, :]
                right = dense[j, k, :] @ dense[i, :, :]
                assert np.array_equal(left % q, right % q)
                total += 1
    return total


def check_shapes(rng):
    total = 0
    for shape in [(1, 1, 1), (2, 3, 2, 1), (2,) * 6, (2, 3, 2, 2, 1, 2, 3, 1), (2,) * 12]:
        data = rng.integers(0, 3, size=shape, dtype=np.uint8)
        for order in ("balanced", "half"):
            variants = [
                compile_tensor(data, order, "mixed"),
                compile_tensor(data, order, "packed"),
                compile_tensor(data, order, "linked"),
                compile_tensor(data, order, tag_policy="compact"),
                compile_tensor(data, order),
            ]
            if not np.any(data == 2):
                variants.append(compile_tensor(data, order, tag_policy="binary_spectral", schedule="min_entries"))
            for tensor in variants:
                for run in tensor.runs:
                    assert run.count > 0
                    for size, x, step in zip(tensor.shape, run.origin, run.step):
                        assert 0 <= x <= x + (run.count - 1) * step < size
                for block in tensor.blocks:
                    for size, start, width, step in zip(tensor.shape, block.origin, block.data.shape, block.step):
                        assert 0 <= start <= start + step * (width - 1) < size
                assert len(tensor.blocks) == 1
            for stage in (variants[1], variants[2]):
                index, values = stage.coo(max_nnz=2_000_000)
                assert len(index) == len({tuple(point) for point in index})
                assert np.all(values > 0)
            assert math.prod(variants[0].shape) == math.prod(shape)
            if len(shape) >= 6:
                assert variants[4].nnz > variants[3].nnz
            total += len(variants)
    return total


def rank_f2(data):
    return _binary_rank([sum(int(x) << i for i, x in enumerate(col)) for col in data.T])


def apply_isomorphism(data, frontal, column, row):
    return np.einsum("ia,jb,ck,ijk->abc", frontal, column, row, data, optimize=True) % 2


def _sub_indices(size, first, extra):
    return list(range(first)) + list(range(first + extra, size + extra))


def check_spectral(rng):
    support_checks = 0
    transport_checks = 0
    for parts in [((2, 1), (2, 1), (1, 2)), ((2, 2), (1, 2), (1, 1, 2)), ((2,), (3,), (2, 2, 2))]:
        shape = tuple(map(sum, parts))
        a_size, v_size, u_size = shape
        r, _, e, ranks = _spectral_data(parts[2])
        expanded = r * u_size
        data = rng.integers(0, 2, size=shape)
        system = make_system(shape)

        def encode(t):
            boxed = CoordinateTensor(shape, (), (DenseBlock((0, 0, 0), t),), system, parts)
            return _delete_binary_spectral(boxed, "binary_spectral").materialize()

        out = encode(data)
        original_frontal = _sub_indices(a_size, parts[0][0], 3)
        original_columns = _sub_indices(v_size, parts[1][0], expanded + sum(e))
        aux = list(range(parts[1][0], parts[1][0] + expanded))
        sets = [(0,), (1,), (2,), (0, 1), (0, 2), (1, 2), (0, 1, 2)]
        markers = out[parts[0][0]:parts[0][0] + 3].transpose(0, 2, 1)
        for x in itertools.product((0, 1), repeat=a_size):
            contaminated = sum(m for a, m in zip(x, out[original_frontal].transpose(0, 2, 1)) if a)
            for s, rank in zip(sets, ranks):
                matrix = (contaminated + markers[list(s)].sum(axis=0)) % 2
                assert rank_f2(matrix) == v_size + rank + sum(e[i] for i in s)
                if len(s) == 1:
                    j = s[0]
                    tag_base = expanded + 3 * v_size
                    rows = [*range(expanded), *range(expanded + j * v_size, expanded + (j + 1) * v_size),
                            *range(tag_base + sum(e[:j]), tag_base + sum(e[:j + 1]))]
                    assert not matrix[list(set(range(matrix.shape[0])) - set(rows))].any()
                    assert rank_f2(matrix) == len(rows)
                    tag_base = parts[1][0] + expanded
                    col_e = list(range(tag_base + sum(e[:j]), tag_base + sum(e[:j + 1])))
                    assert not matrix[:, list(set(range(matrix.shape[1])) - set(original_columns + aux + col_e))].any()
                support_checks += 1

        def elementary_blocks(sizes):
            matrix = np.eye(sum(sizes), dtype=int)
            start = 0
            for n in sizes:
                if n > 1:
                    matrix[start, start + 1] = 1
                start += n
            return matrix

        a_action, v_action, u_action = [elementary_blocks(slice_sizes) for slice_sizes in parts]
        mapped = apply_isomorphism(data, a_action, v_action, u_action)
        ext_a, ext_v, ext_u = [np.eye(n, dtype=int) for n in out.shape]
        ext_a[np.ix_(original_frontal, original_frontal)] = a_action
        ext_v[np.ix_(original_columns, original_columns)] = v_action
        # Every elementary block is an involution over F2.
        lifted = np.kron(u_action, np.eye(r, dtype=int))
        ext_v[np.ix_(aux, aux)] = lifted
        ext_u[:expanded, :expanded] = lifted
        for j in range(3):
            start = expanded + j * v_size
            ext_u[start:start + v_size, start:start + v_size] = v_action
        assert np.array_equal(apply_isomorphism(out, ext_a, ext_v, ext_u), encode(mapped))
        transport_checks += 1

    return support_checks, transport_checks


if __name__ == "__main__":
    random = np.random.default_rng(20261115)
    print("one-axis reference comparisons", check_delete_row(random))
    print("published algebra associativity checks", check_published(random))
    print("full-stage shape and support checks", check_shapes(random))
    print("spectral contamination and explicit witness checks", check_spectral(random))
