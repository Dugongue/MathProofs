"""Independent arithmetic checks for the crossed-flattening benchmark.

Run audit_tensor.py coverage OBJECTS.jsonl or
audit_tensor.py verify PAIRS.jsonl RESULTS.jsonl.
Field conventions are prime integers or "Q". Each tensor is row-major.
"""
import argparse
from collections import Counter
from fractions import Fraction
from itertools import product
import json
from math import prod
from pathlib import Path


class Field:
    def __init__(self, key):
        self.p = None if key == "Q" else int(key)

    def read(self, x):
        if self.p is None:
            return Fraction(str(x))
        if isinstance(x, int):
            return x % self.p
        val = Fraction(str(x))
        return val.numerator * pow(val.denominator, -1, self.p) % self.p

    def cut(self, x):
        return x % self.p if self.p else x

    def inverse(self, x):
        if self.p:
            return pow(x, -1, self.p)
        return Fraction(1, 1) / x


def reduced(rows, field, lead=None):
    work = [list(r) for r in rows]
    stop = len(work[0]) if lead is None else lead
    pivots = []
    for col in range(stop):
        i = len(pivots)
        j = next((j for j in range(i, len(work)) if work[j][col]), None)
        if j is None:
            continue
        work[i], work[j] = work[j], work[i]
        v = field.inverse(work[i][col])
        pivot = work[i] = [field.cut(v * x) for x in work[i]]
        for j, row in enumerate(work):
            if j == i or not row[col]:
                continue
            w = row[col]
            work[j] = [field.cut(x - w * y) for x, y in zip(row, pivot)]
        pivots.append(col)
        if len(pivots) == len(work):
            break
    return work, pivots


def inverse(rows, field):
    n = len(rows)
    augmented = [list(r) + [int(i == j) for j in range(n)] for i, r in enumerate(rows)]
    work, pivots = reduced(augmented, field, lead=n)
    return [r[n:] for r in work] if len(pivots) == n else None, len(pivots)


def multiply(a, b, field):
    columns = list(zip(*b))
    return [[field.cut(sum(x * y for x, y in zip(row, col))) for col in columns] for row in a]


def pack(blocks):
    return [x for block in blocks for x in block]


def tensor_indices(shape):
    return list(product(*(range(n) for n in shape)))


def offset(index, shape):
    value = 0
    for i, n in zip(index, shape):
        value = value * n + i
    return value


def tensor_values(obj, field):
    shape = obj["dims"]
    if "entries" in obj:
        values = obj["entries"]
        if len(values) != prod(shape):
            raise ValueError("Incorrect dense input size")
        return [field.read(x) for x in values]
    values = [0] * prod(shape)
    for index in obj["ones"]:
        flat = offset(index, shape)
        if values[flat]:
            raise ValueError("Duplicate nonzero index")
        values[flat] = 1
    return values


def certify_transport(shape, source, target, matrices, field):
    """Check invertibility and replay the full multilinear action."""
    if len(matrices) != len(shape) or len(source) != prod(shape) or len(target) != prod(shape):
        return False
    transformed = [field.read(x) for x in source]
    wanted = [field.read(x) for x in target]
    indices = tensor_indices(shape)
    for axis, (size, entries) in enumerate(zip(shape, matrices)):
        if len(entries) == size * size and all(not isinstance(x, list) for x in entries):
            entries = [entries[i:i + size] for i in range(0, len(entries), size)]
        if len(entries) != size or any(not isinstance(row, list) or len(row) != size for row in entries):
            return False
        matrix = [[field.read(x) for x in row] for row in entries]
        if len(reduced(matrix, field)[1]) != size:
            return False
        result = []
        for index in indices:
            row = matrix[index[axis]]
            value = sum(row[j] * transformed[offset(index[:axis] + (j,) + index[axis + 1:], shape)]
                        for j in range(size))
            result.append(field.cut(value))
        transformed = result
    return transformed == wanted


def mixed_matrix(tensor, shape, first_pair, second_pair):
    row_shape = [shape[i] for i in first_pair]
    col_shape = [shape[i] for i in second_pair]
    result = []
    for row in tensor_indices(row_shape):
        line = []
        for col in tensor_indices(col_shape):
            index = [0] * 4
            for i, x in zip(first_pair + second_pair, row + col):
                index[i] = x
            line.append(tensor[offset(index, shape)])
        result.append(line)
    return result


def intertwiner_rows(gens, targets, size, field):
    rows = []
    for mat, target in zip(gens, targets):
        for i, j in product(range(size), repeat=2):
            line = [0] * (size * size)
            for k in range(size):
                line[i * size + k] += mat[k][j]
                line[k * size + j] -= target[i][k]
            rows.append([field.cut(x) for x in line])
    return rows


def commutant_rank(gens, size, field):
    return len(reduced(intertwiner_rows(gens, gens, size, field), field)[1])


def classify(shape, values, field, internals=False):
    if len(shape) != 4 or shape[:2] != shape[2:] or min(shape) < 2:
        return {"gate": "format"}
    a, b = shape[:2]
    n = a * b
    f = mixed_matrix(values, shape, (0, 1), (2, 3))
    crossed = mixed_matrix(values, shape, (0, 3), (2, 1))
    fi, rank_f = inverse(f, field)
    gi, rank_crossed = inverse(crossed, field)
    info = {"ranks": [rank_f, rank_crossed], "equal_corank_3_eligible": n - rank_f == 3 and a == b}
    if fi is None or gi is None:
        return {**info, "gate": "singular"}
    h = [[gi[k * b + j][i * b + l] for i, j in product(range(a), range(b))]
         for k, l in product(range(a), range(b))]
    u = multiply(f, h, field)
    for i in range(n):
        u[i][i] = field.cut(u[i][i] - 1)
    u2 = multiply(u, u, field)
    u3 = multiply(u2, u, field)
    one = [
        [[field.cut(sum(z[i * b + j][k * b + j] for j in range(b))) for k in range(a)] for i in range(a)]
        for z in (u2, u3)
    ]
    two = [
        [[field.cut(sum(z[i * b + j][i * b + l] for i in range(a))) for l in range(b)] for j in range(b)]
        for z in (u2, u3)
    ]
    dimensions = [a * a - commutant_rank(one, a, field), b * b - commutant_rank(two, b, field)]
    info = {**info, "gate": "scalar" if dimensions == [1, 1] else "nonscalar", "commutants": dimensions}
    if internals:
        info.update(covariants=(one, two), inverse=fi)
    return info


def rank_signature(shape, values, field):
    cuts = [((i,), tuple(j for j in range(4) if j != i)) for i in range(4)]
    cuts += [((0, i), tuple(j for j in range(1, 4) if j != i)) for i in range(1, 4)]
    return tuple(len(reduced(mixed_matrix(values, shape, a, b), field)[1]) for a, b in cuts)


def independent_verdict(item):
    """Use rank mismatches, then the complete scalar-commutant criterion."""
    shape = item["dims"]
    field = Field(item["field"])
    A = [field.read(x) for x in item["src"]]
    B = [field.read(x) for x in item["dst"]]
    if A == B:
        return "yes", "identical input"
    if rank_signature(shape, A, field) != rank_signature(shape, B, field):
        return "no", "rank certificate"
    first, second = [classify(shape, x, field, internals=True) for x in (A, B)]
    if first.get("commutants") != second.get("commutants"):
        return "no", "commutant dimensions"
    if first["gate"] != "scalar" or second["gate"] != "scalar":
        return "unknown", "outside audit gate"
    inverses = []
    for n, row_ops, col_ops in zip(shape, first["covariants"], second["covariants"]):
        system = intertwiner_rows(row_ops, col_ops, n, field)
        work, pivots = reduced(system, field)
        free = [i for i in range(n*n) if i not in pivots]
        if len(free) != 1:
            return "no", "intertwiner dimension"
        g = [0] * (n*n)
        g[free[0]] = 1
        for row, pivot in zip(work, pivots):
            g[pivot] = field.cut(-row[free[0]])
        inv, _ = inverse([g[i:i+n] for i in range(0, n*n, n)], field)
        if inv is None:
            return "no", "local singularity"
        inverses.append(inv)
    a, b = shape[:2]
    L_inv = [[field.cut(inverses[0][i][k] * inverses[1][j][l]) for k, l in tensor_indices((a,b))]
             for i, j in tensor_indices((a,b))]
    original_target = mixed_matrix(B, shape, (0,1), (2,3))
    R_t = multiply(multiply(first["inverse"], L_inv, field), original_target, field)
    grouped = [[R_t[i*b+j][k*b+l] for j, l in tensor_indices((b,b))] for i, k in tensor_indices((a,a))]
    rank = len(reduced(grouped, field)[1])
    return ("yes" if rank == 1 else "no"), "Kronecker rank"


def coverage_record(obj, screen_prime=None):
    displayed = Field(obj["field"])
    shape = obj["dims"]
    if screen_prime is not None and displayed.p is None:
        try:
            mod = Field(screen_prime)
            res = classify(shape, tensor_values(obj, mod), mod)
        except ValueError:
            res = {}
        if res.get("gate") == "scalar":
            res["method"] = "modular-nonzero-minor-certificate-for-Q"
            return {"id": obj["id"], **res}
    return {"id": obj["id"], **classify(shape, tensor_values(obj, displayed), displayed), "method": "exact"}


def records(path):
    with path.open(encoding="utf-8") as handle:
        for line in handle:
            if line.strip():
                yield json.loads(line)


def verify_results(pairs, results, check_no=False):
    by_id = {p["id"]: p for p in pairs}
    seen = Counter()
    for record in results:
        item = by_id[record["id"]]
        status = record["status"]
        if status == "yes":
            if not certify_transport(item["dims"], item["src"], item["dst"], record["witness"], Field(item["field"])):
                raise ValueError(f"Bad witness for {record['id']}")
            seen["verified_yes"] += 1
        elif status in ("no", "unknown"):
            seen[status] += 1
            if check_no and status == "no":
                independent, reason = independent_verdict(item)
                if independent == "yes":
                    raise ValueError(f"False negative for {record['id']}")
                seen[f"no_{independent}_{reason}"] += 1
        else:
            raise ValueError(f"Unrecognized status for {record['id']}")
    return dict(seen)


def main():
    cli = argparse.ArgumentParser(description=__doc__)
    modes = cli.add_subparsers(dest="mode", required=True)
    coverage = modes.add_parser("coverage")
    coverage.add_argument("objects", type=Path)
    coverage.add_argument("--screen-prime", type=int)
    verify = modes.add_parser("verify")
    verify.add_argument("pairs", type=Path)
    verify.add_argument("results", type=Path)
    verify.add_argument("--check-no", action="store_true")
    args = cli.parse_args()
    if args.mode == "coverage":
        for obj in records(args.objects):
            print(json.dumps(coverage_record(obj, args.screen_prime), separators=(",", ":")))
    else:
        print(json.dumps(verify_results(records(args.pairs), records(args.results), args.check_no), sort_keys=True))


if __name__ == "__main__":
    main()
