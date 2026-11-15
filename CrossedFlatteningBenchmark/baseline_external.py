"""Exact direct tensor-isomorphism adapters for CaDiCaL and Z3.

The adapter uses bidirectional mode transforms of the original input. Public
solver engines are unmodified. SAT witnesses always undergo an independent
exact check. Over Q, non-rational real models are unresolved.
"""
import argparse
from fractions import Fraction
from itertools import combinations, permutations, product
import json
from math import gcd, isqrt, lcm, prod
from pathlib import Path
import subprocess
import tempfile
from time import perf_counter


def prime_field(value):
    return (type(value) is int and value >= 2 and
            all(value % x for x in range(2, isqrt(value) + 1)))


def parse_pair(pair):
    field = pair["field"]
    dims = tuple(pair["dims"])
    if len(dims) < 2 or any(type(n) is not int or n < 1 for n in dims):
        raise ValueError("expected at least two positive mode dimensions")
    if field != "Q" and not prime_field(field):
        raise ValueError("expected a prime field or Q")
    src = pair["src"]
    dst = pair["dst"]
    if len(src) != prod(dims) or len(dst) != prod(dims):
        raise ValueError("wrong array length")
    if field == "Q":
        if any(type(x) not in (int, str) for x in src + dst):
            raise ValueError("exact rationals require an integer or a string")
        return field, dims, list(map(Fraction, src)), list(map(Fraction, dst))
    if any(type(x) is not int or not 0 <= x < field for x in src + dst):
        raise ValueError("coefficient outside the prime field")
    return field, dims, src, dst


def eliminate(matrix, field, augmented=False):
    m, n = len(matrix), len(matrix[0])
    rows = [a[:] + [int(i == j) for j in range(n)] if augmented else a[:]
            for i, a in enumerate(matrix)]
    if field == "Q":
        rows = [list(map(Fraction, row)) for row in rows]
    pivot_row = 0
    for j in range(n):
        pivot = next((i for i in range(pivot_row, m) if rows[i][j]), None)
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        leading = rows[pivot_row][j]
        recip = 1 / leading if field == "Q" else pow(leading, -1, field)
        clean = rows[pivot_row][j:]
        rows[pivot_row][j:] = [x * recip if field == "Q" else x * recip % field
                                for x in clean]
        pivot_values = rows[pivot_row][j:]
        start = 0 if augmented else pivot_row + 1
        for i in range(start, m):
            entry = rows[i][j]
            if i == pivot_row or not entry:
                continue
            values = (a - entry * b for a, b in zip(rows[i][j:], pivot_values))
            rows[i][j:] = list(values) if field == "Q" else [x % field for x in values]
        pivot_row += 1
        if pivot_row == m:
            break
    if not augmented:
        return pivot_row
    return [row[n:] for row in rows] if pivot_row == n else None


def rank_signature(field, dims, data):
    facets = set()
    for r in range(1, min(2, len(dims) - 1) + 1):
        for cut in combinations(range(len(dims)), r):
            other = tuple(i for i in range(len(dims)) if i not in cut)
            facets.add(min(cut, other))
    strides = [prod(dims[i + 1:]) for i in range(len(dims))]
    signatures = []
    for cut in sorted(facets):
        other = [i for i in range(len(dims)) if i not in cut]
        def offsets(modes):
            return [sum(a * strides[b] for a, b in zip(index, modes))
                    for index in product(*(range(dims[i]) for i in modes))]
        row_offsets, col_offsets = offsets(cut), offsets(other)
        matrix = [[data[i + j] for j in col_offsets] for i in row_offsets]
        signatures.append(eliminate(matrix, field))
    return signatures


def fiber_step(values, dims, mode, matrix, row_function):
    side = dims[mode]
    stride = prod(dims[mode + 1:])
    out = [None] * len(values)
    for start in range(0, len(values), side * stride):
        for index in range(start, start + stride):
            column = values[index : index + side * stride : stride]
            for row, coefficients in enumerate(matrix):
                out[index + row * stride] = row_function(coefficients, column)
    return out


def verify_witness(field, dims, src, dst, witness):
    if any(eliminate(matrix, field) != n for n, matrix in zip(dims, witness)):
        return False
    def row_product(row, col):
        value = sum(x * y for x, y in zip(row, col))
        return value if field == "Q" else value % field
    data = src
    for mode, matrix in enumerate(witness):
        data = fiber_step(data, dims, mode, matrix, row_product)
    return data == dst


def exact_witness(field, dims, src, dst, maps):
    # On the right side of the equation the model maps dst backwards.
    # Invert its right-half matrices to get a single witness src -> dst.
    split = len(dims) // 2
    witness = maps[:split] + [eliminate(matrix, field, augmented=True)
                             for matrix in maps[split:]]
    if any(matrix is None for matrix in witness) or not verify_witness(field, dims, src, dst, witness):
        raise ArithmeticError("external model did not verify on the original tensors")
    return witness


class BinaryCircuit:
    # Integer literals 1 and -1 are true and false, respectively.
    def __init__(self):
        self.variables = 1
        self.clauses = [(1,)]
        self.gates = {}

    def new(self):
        self.variables += 1
        return self.variables

    def conjunction(self, a, b):
        if a == -1 or b == -1 or a == -b:
            return -1
        if a == 1 or a == b:
            return b
        if b == 1:
            return a
        key = (0, min(a, b), max(a, b))
        if key not in self.gates:
            c = self.new()
            self.gates[key] = c
            self.clauses.extend(((-a, -b, c), (a, -c), (b, -c)))
        return self.gates[key]

    def xor(self, a, b):
        if a == -1:
            return b
        if b == -1:
            return a
        if a == 1:
            return -b
        if b == 1:
            return -a
        if a == b:
            return -1
        if a == -b:
            return 1
        sign = 1 if a * b > 0 else -1
        a, b = sorted((abs(a), abs(b)))
        key = (1, a, b)
        if key not in self.gates:
            c = self.new()
            self.gates[key] = c
            self.clauses.extend(((-a, -b, -c), (a, b, -c), (a, -b, c), (-a, b, c)))
        return sign * self.gates[key]

    def parity(self, values):
        sign = False
        bits = set()
        for value in values:
            if value == 1:
                sign = not sign
            elif value != -1:
                if value < 0:
                    sign = not sign
                    value = -value
                if value in bits:
                    bits.remove(value)
                else:
                    bits.add(value)
        result = -1
        for literal in sorted(bits):
            result = self.xor(result, literal)
        return -result if sign else result

    def dot(self, row, col):
        return self.parity(self.conjunction(a, b) for a, b in zip(row, col))

    def invertible(self, matrix):
        n = len(matrix)
        if n <= 3:
            terms = []
            for perm in permutations(range(n)):
                term = 1
                for i in range(n):
                    term = self.conjunction(term, matrix[i][perm[i]])
                terms.append(term)
            self.clauses.append((self.parity(terms),))
            return
        inverse = [[self.new() for _ in range(n)] for _ in range(n)]
        for i, row in enumerate(matrix):
            for j, col in enumerate(zip(*inverse)):
                value = self.dot(row, col)
                self.clauses.append((value if i == j else -value,))


def build_binary(dims, src, dst):
    circ = BinaryCircuit()
    matrices = [[[circ.new() for _ in range(n)] for _ in range(n)] for n in dims]
    transformed_src = [1 if x else -1 for x in src]
    transformed_dst = [1 if x else -1 for x in dst]
    split = len(dims) // 2
    for mode, matrix in enumerate(matrices):
        circ.invertible(matrix)
        if mode < split:
            transformed_src = fiber_step(transformed_src, dims, mode, matrix, circ.dot)
        else:
            transformed_dst = fiber_step(transformed_dst, dims, mode, matrix, circ.dot)
    for a, b in zip(transformed_src, transformed_dst):
        if a != b:
            circ.clauses.extend(((-a, b), (a, -b)))
    return circ, matrices


def solve_cadical(field, dims, src, dst, executable, budget, scratch):
    if field != 2:
        return {"status": "unknown", "reason": "CaDiCaL adapter supports GF(2)"}
    if executable is None:
        raise ValueError("supply --executable pointing to the CaDiCaL binary")
    build_start = perf_counter()
    circ, variables = build_binary(dims, src, dst)
    remaining = budget - (perf_counter() - build_start)
    if remaining <= 0:
        return {"status": "unknown", "reason": "encoding deadline"}
    file = None
    result = {"variables": circ.variables, "clauses": len(circ.clauses)}
    try:
        with tempfile.NamedTemporaryFile("w", dir=scratch, prefix="tensor-",
                                         suffix=".cnf", delete=False,
                                         encoding="ascii", newline="\n") as stream:
            file = Path(stream.name)
            stream.write(f"p cnf {circ.variables} {len(circ.clauses)}\n")
            stream.writelines(" ".join(map(str, clause)) + " 0\n" for clause in circ.clauses)
        result["encoding_seconds"] = perf_counter() - build_start
        run_start = perf_counter()
        remaining = budget - result["encoding_seconds"]
        if remaining <= 0:
            return dict(result, status="unknown", reason="encoding deadline")
        try:
            execution = subprocess.run([str(executable), "-q", str(file)],
                                       capture_output=True, text=True,
                                       timeout=remaining, check=False)
        except subprocess.TimeoutExpired:
            return dict(result, status="unknown", reason="solver timeout",
                        solver_seconds=perf_counter() - run_start)
        result["solver_seconds"] = perf_counter() - run_start
        lines = execution.stdout.splitlines()
        if execution.returncode == 20 and "s UNSATISFIABLE" in lines:
            return dict(result, status="no", reason="UNSAT")
        if execution.returncode != 10 or "s SATISFIABLE" not in lines:
            return dict(result, status="unknown", reason=f"solver exit {execution.returncode}")
        start_verify = perf_counter()
        true = {int(x) for line in lines if line.startswith("v ")
                for x in line[2:].split() if int(x) > 0}
        maps = [[[int(x in true) for x in row] for row in mat] for mat in variables]
        witness = exact_witness(field, dims, src, dst, maps)
        return dict(result, status="yes", witness=witness,
                    verify_seconds=perf_counter() - start_verify)
    finally:
        if file is not None:
            file.unlink(missing_ok=True)


def solve_z3(field, dims, src, dst, budget):
    build_start = perf_counter()
    try:
        import z3
    except ImportError:
        return {"status": "unknown", "reason": "z3-solver is not installed"}
    if field == "Q":
        solver = z3.SolverFor("QF_NRA")
        const = lambda x: z3.RealVal(str(x))
        variable = z3.Real
        add = z3.Sum
    else:
        solver = z3.SolverFor("QF_BV")
        # Maximum unreduced sum is one size-n field dot product.
        width = (max(dims) * (field - 1) ** 2 + field).bit_length()
        const = lambda x: z3.BitVecVal(x, width)
        variable = lambda name: z3.BitVec(name, width)
        def add(terms):
            return z3.URem(sum(terms, const(0)), const(field))
    matrices = [[[variable(f"g{k}_{i}_{j}") for j in range(n)] for i in range(n)]
                for k, n in enumerate(dims)]
    def dot(row, col):
        return add([x * y for x, y in zip(row, col)])
    transformed_src, transformed_dst = list(map(const, src)), list(map(const, dst))
    for axis, matrix in enumerate(matrices):
        n = dims[axis]
        if field == "Q" and n <= 3:
            determinant = []
            for perm in permutations(range(n)):
                parity = sum(x > y for i, x in enumerate(perm) for y in perm[i + 1:]) % 2
                determinant.append((-1 if parity else 1) * prod(matrix[i][j] for i, j in enumerate(perm)))
            solver.add(z3.Sum(determinant) != 0)
        else:
            inverse = [[variable(f"h{axis}_{i}_{j}") for j in range(n)] for i in range(n)]
            if field != "Q":
                solver.add(*(z3.ULT(x, const(field)) for block in (matrix, inverse)
                             for row in block for x in row))
            for i, row in enumerate(matrix):
                for j, col in enumerate(zip(*inverse)):
                    solver.add(dot(row, col) == const(int(i == j)))
        if axis < len(dims) // 2:
            transformed_src = fiber_step(transformed_src, dims, axis, matrix, dot)
        else:
            transformed_dst = fiber_step(transformed_dst, dims, axis, matrix, dot)
    solver.add(*(a == b for a, b in zip(transformed_src, transformed_dst)))
    result = {"encoding_seconds": perf_counter() - build_start,
              "engine_version": z3.get_version_string()}
    remaining = budget - result["encoding_seconds"]
    if remaining <= 0:
        return dict(result, status="unknown", reason="encoding deadline")
    solver.set(timeout=max(1, int(1000 * remaining)))
    t0 = perf_counter()
    verdict = solver.check()
    result["solver_seconds"] = perf_counter() - t0
    if verdict == z3.unsat:
        # In the rational case no real solution implies no rational solution.
        return dict(result, status="no", reason="UNSAT")
    if verdict != z3.sat:
        return dict(result, status="unknown", reason=solver.reason_unknown())
    t0 = perf_counter()
    model = solver.model()
    maps = []
    for block in matrices:
        vals = [[model.eval(x, model_completion=True) for x in row] for row in block]
        if field == "Q":
            if any(not z3.is_rational_value(x) for row in vals for x in row):
                return dict(result, status="unknown", reason="real model has non-rational entries")
            maps.append([[Fraction(x.numerator_as_long(), x.denominator_as_long()) for x in row]
                         for row in vals])
        else:
            maps.append([[x.as_long() for x in row] for row in vals])
    witness = exact_witness(field, dims, src, dst, maps)
    if field == "Q":
        witness = [[[str(x) for x in row] for row in matrix] for matrix in witness]
    return dict(result, status="yes", witness=witness, verify_seconds=perf_counter() - t0)


def rational_reconstruct(residue, modulus):
    bound = isqrt(modulus // 2)
    a, b = modulus, residue
    c, d = 0, 1
    while b > bound:
        q, r = divmod(a, b)
        a, b = b, r
        c, d = d, c - q * d
    if d < 0:
        b, d = -b, -d
    if not 0 < d <= bound or gcd(b, d) != 1 or (b - residue * d) % modulus:
        return None
    return Fraction(b, d)


def apply_modular(data, dims, maps, modulus):
    def dot(row, col):
        return sum(a * b for a, b in zip(row, col)) % modulus
    for axis, matrix in enumerate(maps):
        data = fiber_step(data, dims, axis, matrix, dot)
    return data


def derivative_columns(data, dims, maps, indices, prime):
    columns = []
    for axis, i, j in indices:
        tangent = [[int(x == i and y == j) for y in range(dims[axis])]
                   for x in range(dims[axis])]
        derivative_maps = maps[:]
        derivative_maps[axis] = tangent
        columns.append(apply_modular(data, dims, derivative_maps, prime))
    return columns


def prepare_binary_elimination(columns):
    # Work in column span and carry a preimage for each basis vector.  A
    # right-hand side outside this span cannot be lifted from the current root.
    pivots = {}
    for i, values in enumerate(columns):
        bits = sum(x << j for j, x in enumerate(values))
        solution = 1 << i
        while bits:
            slot = bits.bit_length() - 1
            if slot not in pivots:
                pivots[slot] = bits, solution
                break
            old_bits, old_solution = pivots[slot]
            bits ^= old_bits
            solution ^= old_solution
    def solve(values):
        bits = sum(x << j for j, x in enumerate(values))
        solution = 0
        while bits:
            slot = bits.bit_length() - 1
            if slot not in pivots:
                return None
            old_bits, old_solution = pivots[slot]
            bits ^= old_bits
            solution ^= old_solution
        return [solution >> i & 1 for i in range(len(columns))]
    return solve, len(pivots)


def solve_hensel(field, dims, src, dst, executable, budget, scratch):
    """Try verified rational reconstruction from a CaDiCaL binary solution."""
    if field != "Q":
        return {"status": "unknown", "reason": "lifting adapter needs Q"}
    started = perf_counter()
    denominator = lcm(*(x.denominator for x in src + dst))
    a, b = ([int(x * denominator) for x in data] for data in (src, dst))
    content = gcd(*a, *b)
    if content:
        a, b = [x // content for x in a], [x // content for x in b]
    reduction_start = perf_counter()
    search = solve_cadical(2, dims, [x & 1 for x in a], [x & 1 for x in b],
                           executable, budget - (reduction_start - started), scratch)
    result = {k: v for k, v in search.items() if k not in {"status", "witness", "reason"}}
    result["mod2_seconds"] = perf_counter() - reduction_start
    if search["status"] != "yes":
        return dict(result, status="unknown", reason="binary seed unavailable: " +
                    search.get("reason", search["status"]))
    maps = search["witness"]
    # Fix one nonzero pivot in all but the last mode.  Their modulo-two value
    # is already one.  Rescaling can be compensated by the last mode.
    frozen = set()
    for axis, matrix in enumerate(maps[:-1]):
        i, j = next((i, j) for i, row in enumerate(matrix) for j, x in enumerate(row) if x)
        frozen.add((axis, i, j))
    indices = [(axis, i, j) for axis, n in enumerate(dims) for i in range(n)
               for j in range(n) if (axis, i, j) not in frozen]
    lift_start = perf_counter()
    solve, rank = prepare_binary_elimination(derivative_columns([x & 1 for x in a],
                                                dims, maps, indices, 2))
    result.update(jacobian_rank=rank, jacobian_columns=len(indices))
    modulus = 2
    for precision in range(2, 65):
        if perf_counter() - started >= budget:
            return dict(result, status="unknown", reason="lifting deadline",
                        lift_seconds=perf_counter() - lift_start)
        next_modulus = 2 * modulus
        c = apply_modular([x % next_modulus for x in a], dims, maps, next_modulus)
        error = [(y - x) % next_modulus for x, y in zip(c, b)]
        if any(value % modulus for value in error):
            raise ArithmeticError("lifting invariant failed")
        correction = solve([value // modulus for value in error])
        if correction is None:
            return dict(result, status="unknown", reason="binary seed did not lift",
                        lift_seconds=perf_counter() - lift_start)
        for (axis, i, j), value in zip(indices, correction):
            maps[axis][i][j] += modulus * value
        modulus = next_modulus
        if precision not in (8, 16, 24, 32, 48, 64):
            continue
        verify_start = perf_counter()
        reconstructed = [[[rational_reconstruct(x, modulus) for x in row]
                          for row in matrix] for matrix in maps]
        if (all(x is not None for matrix in reconstructed for row in matrix for x in row)
                and verify_witness("Q", dims, src, dst, reconstructed)):
            witness = [[[str(x) for x in row] for row in matrix] for matrix in reconstructed]
            return dict(result, status="yes", witness=witness, lift_bits=precision,
                        verify_seconds=perf_counter() - verify_start,
                        lift_seconds=verify_start - lift_start)
    return dict(result, status="unknown", reason="no verified rational reconstruction",
                lift_seconds=perf_counter() - lift_start)

def solve_file(path, backend, timeout, executable=None, scratch=None, rank_filter=True):
    start = perf_counter()
    pair = json.loads(Path(path).read_text(encoding="utf-8-sig"))
    field, dims, src, dst = parse_pair(pair)
    read_seconds = perf_counter() - start
    rank_start = perf_counter()
    if src == dst:
        witness = [[[int(i == j) for j in range(n)] for i in range(n)] for n in dims]
        result = {"status": "yes", "reason": "identical input",
                  "witness": witness, "verify_seconds": 0}
    elif rank_filter and rank_signature(field, dims, src) != rank_signature(field, dims, dst):
        result = {"status": "no", "reason": "flattening rank mismatch"}
    else:
        rank_seconds = perf_counter() - rank_start
        remaining = timeout - (perf_counter() - start)
        if remaining <= 0:
            result = {"status": "unknown", "reason": "preprocessing deadline"}
        elif backend == "cadical":
            result = solve_cadical(field, dims, src, dst, executable, remaining, scratch)
        elif backend == "z3":
            result = solve_z3(field, dims, src, dst, remaining)
        elif backend == "hensel":
            result = solve_hensel(field, dims, src, dst, executable, remaining, scratch)
        else:
            raise ValueError("unknown backend")
        result["rank_seconds"] = rank_seconds
    result.setdefault("rank_seconds", perf_counter() - rank_start)
    result.update(id=pair.get("id", Path(path).stem), solver=backend, field=field,
                  dims=dims, elapsed_seconds=perf_counter() - start, read_seconds=read_seconds)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--backend", choices=("cadical", "z3", "hensel"), required=True)
    parser.add_argument("--executable", type=Path, help="path to the CaDiCaL executable")
    parser.add_argument("--timeout", type=float, default=10)
    parser.add_argument("--scratch", type=Path, help="optional scratch directory for DIMACS")
    parser.add_argument("--no-rank-filter", action="store_true")
    parser.add_argument("pairs", nargs="+", type=Path)
    args = parser.parse_args()
    for pair in args.pairs:
        report = solve_file(pair, args.backend, args.timeout, args.executable,
                            args.scratch, not args.no_rank_filter)
        print(json.dumps(report), flush=True)


if __name__ == "__main__":
    main()
