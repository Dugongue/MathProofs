"""Exhaustive small-field checks of the unitary generation argument."""
from itertools import permutations, product
import json


def field_operations(size, polynomial):
    def mul(a, b):
        out = 0
        while b:
            if b & 1:
                out ^= a
            b >>= 1
            a <<= 1
            if a & size:
                a ^= polynomial
        return out

    multiples = [[mul(a, b) for b in range(size)] for a in range(size)]

    def power(x, e):
        result = 1
        for _ in range(e):
            result = mul(result, x)
        return result

    return multiples, power


def controls(size, q, polynomial, n):
    table, power = field_operations(size, polynomial)
    conjugates = [power(x, q) for x in range(size)]

    def inner(v, w):
        answer = 0
        for a, b in zip(v, w, strict=True):
            answer ^= table[conjugates[a]][b]
        return answer

    def determinant(columns):
        answer = 0
        for p in permutations(range(n)):
            term = 1
            for j, i in enumerate(p):
                term = table[term][columns[j][i]]
            answer ^= term
        return answer

    def apply(columns, v):
        output = []
        for i in range(n):
            entry = 0
            for col, x in zip(columns, v, strict=True):
                entry ^= table[col[i]][x]
            output.append(entry)
        return tuple(output)

    vectors = list(product(range(size), repeat=n))
    norm_one = [v for v in vectors if inner(v, v) == 1]
    orthogonal = {v: {w for w in norm_one if inner(v, w) == 0} for v in norm_one}

    def frames(prefix):
        if len(prefix) == n:
            yield prefix
            return
        choices = norm_one if not prefix else set.intersection(*(orthogonal[v] for v in prefix))
        for v in choices:
            yield from frames(prefix + (v,))

    unitary = list(frames(()))
    special_unitary = [columns for columns in unitary if determinant(columns) == 1]
    assert {columns[0] for columns in special_unitary} == set(norm_one)

    answer = {"field_order": size, "unitary_order": len(unitary),
              "special_unitary_order": len(special_unitary),
              "norm_one_vectors": len(norm_one),
              "special_unitary_orbit_of_first_basis_vector": len({c[0] for c in special_unitary})}
    if q > 2 and n == 2:
        fixed_field = [t for t in range(2, size) if power(t, q) == t]
        assert fixed_field
        scalar = fixed_field[0]
        isotropic = [v for v in vectors if any(v) and inner(v, v) == 0]
        for v in isotropic:
            scaled = tuple(table[scalar][x] for x in v)
            assert any(apply(g, v) == scaled for g in special_unitary)
        fixed_nonzero_norms = {inner(v, v) for v in vectors} - {0}
        for norm in fixed_nonzero_norms:
            values = {v for v in vectors if inner(v, v) == norm}
            rep = next(iter(values))
            assert {apply(g, rep) for g in special_unitary} == values
        answer["nonzero_isotropic_vectors_rescaled_by_special_unitary"] = len(isotropic)
        answer["nonzero_norm_classes_individually_transitive"] = len(fixed_nonzero_norms)
    return answer


if __name__ == "__main__":
    print(json.dumps({"SU3_q2": controls(4, 2, 0b111, 3),
                      "SU2_q4": controls(16, 4, 0b10011, 2)}, indent=2))
