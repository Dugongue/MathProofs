"""Independent exact direct GF(2) tensor-isomorphism baseline using CaDiCaL.

The encoding uses an independent invertible matrix per mode. Apply the matrices
one at a time using multiply = AND and add = XOR, and constrain the resulting
tensor to equal the second input. All circuit gates have Tseitin definitions.
"""
import argparse
import json
from itertools import permutations
from math import prod
from pathlib import Path
import subprocess
import tempfile
import time

from baseline_io import read_pair


class Circuit:
    def __init__(self):
        self.variables = 0
        self.clauses = []
        self.true = self.new_var()
        self.false = -self.true
        self.clause(self.true)

    def new_var(self):
        self.variables += 1
        return self.variables

    def clause(self, *literals):
        self.clauses.append(literals)

    def gate_and(self, a, b):
        if a == self.true or a == b:
            return b
        if b == self.true:
            return a
        if a == self.false or b == self.false or a == -b:
            return self.false
        c = self.new_var()
        self.clause(-a, -b, c)
        self.clause(a, -c)
        self.clause(b, -c)
        return c

    def gate_xor(self, a, b):
        if a == self.false:
            return b
        if b == self.false:
            return a
        if a == self.true:
            return -b
        if b == self.true:
            return -a
        if a == b:
            return self.false
        if a == -b:
            return self.true
        c = self.new_var()
        self.clause(-a, -b, -c)
        self.clause(a, b, -c)
        self.clause(a, -b, c)
        self.clause(-a, b, c)
        return c

    def parity(self, literals):
        result = self.false
        for literal in literals:
            result = self.gate_xor(result, literal)
        return result

    def conjunction(self, literals):
        result = self.true
        for literal in literals:
            result = self.gate_and(result, literal)
        return result

    def boolean(self, bit):
        return self.true if bit else self.false

    def dimacs(self, path):
        with path.open("w", encoding="ascii", newline="\n") as stream:
            stream.write(f"p cnf {self.variables} {len(self.clauses)}\n")
            for clause in self.clauses:
                stream.write(" ".join(map(str, clause)) + " 0\n")


def add_invertibility(circuit, matrix):
    size = len(matrix)
    if size <= 3:
        determinant = circuit.parity(
            circuit.conjunction(matrix[row][col] for row, col in enumerate(perm))
            for perm in permutations(range(size))
        )
        circuit.clause(determinant)
        return
    inverse = [[circuit.new_var() for _ in range(size)] for _ in range(size)]
    for row in range(size):
        for col in range(size):
            entry = circuit.parity(
                circuit.gate_and(matrix[row][k], inverse[k][col]) for k in range(size)
            )
            circuit.clause(entry if row == col else -entry)


def step(circuit, previous, dims, mode, matrix):
    side = dims[mode]
    stride = prod(dims[mode + 1:])
    output = [0] * len(previous)
    for block in range(0, len(previous), stride * side):
        for index in range(block, block + stride):
            for row in range(side):
                output[index + row * stride] = circuit.parity(
                    circuit.gate_and(matrix[row][column], previous[index + column * stride])
                    for column in range(side)
                )
    return output


def build_circuit(prime, dims, source, target):
    if prime != 2:
        raise ValueError("CaDiCaL baseline needs GF(2)")
    circuit = Circuit()
    transforms = [[[circuit.new_var() for _ in range(n)] for _ in range(n)] for n in dims]
    values = [circuit.boolean(x) for x in source]
    for axis, transform in enumerate(transforms):
        add_invertibility(circuit, transform)
        values = step(circuit, values, dims, axis, transform)
    for literal, expected in zip(values, target):
        circuit.clause(literal if expected else -literal)
    return circuit, transforms


def invertible(matrix):
    # Independent rank test on row spans.
    width = len(matrix)
    span = {0}
    for row in matrix:
        word = sum(value << i for i, value in enumerate(row))
        span |= {value ^ word for value in span}
    return len(span) == 1 << width


def verify_witness(dims, source, target, matrices):
    data = list(source)
    for axis, matrix in enumerate(matrices):
        side = dims[axis]
        if not invertible(matrix):
            return False
        stride = prod(dims[axis + 1:])
        update = [0] * len(data)
        for start in range(0, len(data), side * stride):
            for i in range(start, start + stride):
                for row in range(side):
                    update[i + row * stride] = sum(
                        matrix[row][column] * data[i + column * stride]
                        for column in range(side)
                    ) % 2
        data = update
    return data == target


def solve_file(path, executable, timeout):
    start = time.perf_counter()
    prime, dims, source, target = read_pair(path)
    read_s = time.perf_counter() - start
    with tempfile.TemporaryDirectory(prefix="balanced-ti-cadical-") as temp:
        dimacs = Path(temp) / "tensor.cnf"
        build_start = time.perf_counter()
        circuit, transforms = build_circuit(prime, dims, source, target)
        circuit.dimacs(dimacs)
        result = {"case": path.name, "format": dims, "read_s": read_s,
                  "build_s": time.perf_counter() - build_start,
                  "dimacs_bytes": dimacs.stat().st_size, "variables": circuit.variables,
                  "clauses": len(circuit.clauses)}
        solve_start = time.perf_counter()
        try:
            run = subprocess.run([str(executable), "-q", str(dimacs)], capture_output=True,
                                 check=False, text=True, timeout=timeout)
            lines = run.stdout.splitlines()
            if run.returncode == 10 and "s SATISFIABLE" in lines:
                check_start = time.perf_counter()
                true_variables = {
                    int(literal) for line in lines if line.startswith("v ")
                    for literal in line[2:].split() if int(literal) > 0
                }
                matrices = [[[int(var in true_variables) for var in row]
                             for row in matrix] for matrix in transforms]
                if not verify_witness(dims, source, target, matrices):
                    raise ValueError("CaDiCaL witness did not verify against original tensor")
                result.update(status="decided", isomorphic=True, witness=matrices,
                              verify_s=time.perf_counter() - check_start)
            elif run.returncode == 20 and "s UNSATISFIABLE" in lines:
                result.update(status="decided", isomorphic=False)
            else:
                result.update(status="error", returncode=run.returncode,
                              diagnostic=(run.stdout + run.stderr)[-500:])
        except subprocess.TimeoutExpired:
            result["status"] = "timeout"
        result["solver_including_process_s"] = time.perf_counter() - solve_start - result.get("verify_s", 0)
    result["total_s"] = time.perf_counter() - start
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cadical", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=8)
    parser.add_argument("--repeats", type=int, default=1)
    parser.add_argument("cases", type=Path, nargs="+")
    args = parser.parse_args()
    for rep in range(args.repeats):
        for path in args.cases:
            result = solve_file(path, args.cadical, args.timeout)
            result["repeat"] = rep
            print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
