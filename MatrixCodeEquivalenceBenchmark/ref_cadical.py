"""Prime-field matrix-code equivalence encoded as a CaDiCaL SAT problem."""
import argparse
import json
from pathlib import Path
import subprocess
import tempfile
from time import perf_counter

from ref_io import read_pair, verify


class ConstructionLimit(Exception):
    pass


class Circuit:
    def __init__(self, output, p, max_clauses):
        self.output = output
        self.p = p
        self.width = (p - 1).bit_length()
        self.variables = 1
        self.clauses = 0
        self.limit = max_clauses
        self.true = 1
        self.false = -1
        self.clause(self.true)
        self.zero = self.constant(0)
        self.one = self.constant(1)

    def var(self):
        self.variables += 1
        return self.variables

    def clause(self, *lits):
        reduced = set(lits)
        if self.true in reduced or any(a != self.false and -a in reduced for a in reduced):
            if self.clauses or lits != (self.true,):
                return
        reduced.discard(self.false)
        self.clauses += 1
        if self.clauses > self.limit:
            raise ConstructionLimit
        self.output.write(" ".join(map(str, sorted(reduced))) + " 0\n")

    def and_(self, a, b):
        if a == b or b == self.true:
            return a
        if a == self.true:
            return b
        if a == -b or self.false in (a, b):
            return self.false
        c = self.var()
        self.clause(-a, -b, c)
        self.clause(a, -c)
        self.clause(b, -c)
        return c

    def or_(self, a, b):
        return -self.and_(-a, -b)

    def xor(self, a, b):
        if a == b:
            return self.false
        if a == -b:
            return self.true
        if a == self.false:
            return b
        if b == self.false:
            return a
        if a == self.true:
            return -b
        if b == self.true:
            return -a
        c = self.var()
        self.clause(-c, a, b)
        self.clause(-c, -a, -b)
        self.clause(c, a, -b)
        self.clause(c, -a, b)
        return c

    def constant(self, val, width=None):
        return tuple(self.true if val >> i & 1 else self.false
                     for i in range(self.width if width is None else width))

    def ge_const(self, bits, bound):
        greater_equal = self.true
        for i, bit in enumerate(bits):
            greater_equal = (self.and_(greater_equal, bit) if bound >> i & 1
                             else self.or_(greater_equal, bit))
        return greater_equal

    def fieldvar(self):
        x = tuple(self.var() for _ in range(self.width))
        if self.p < 1 << self.width:
            self.clause(-self.ge_const(x, self.p))
        return x

    def eq(self, a, b):
        for x, y in zip(a, b):
            self.clause(-x, y)
            self.clause(x, -y)

    def add_plain(self, a, b):
        result = []
        carry = self.false
        for i, (x, y) in enumerate(zip(a, b)):
            different = self.xor(x, y)
            result.append(self.xor(different, carry))
            if i + 1 < len(a):
                carry = self.or_(self.and_(x, y), self.and_(different, carry))
        return tuple(result)

    def add(self, a, b):
        if a == self.zero:
            return b
        if b == self.zero:
            return a
        if self.p == 2:
            return (self.xor(a[0], b[0]),)
        padded = self.add_plain(a + (self.false,), b + (self.false,))
        subtract = self.ge_const(padded, self.p)
        delta = self.add_plain(padded, self.constant(-self.p, self.width + 1))
        return tuple(self.or_(self.and_(subtract, d), self.and_(-subtract, v))
                     for v, d in zip(padded[:self.width], delta))

    def mul(self, a, b):
        if a == self.zero or b == self.zero:
            return self.zero
        if a == self.one:
            return b
        if b == self.one:
            return a
        if self.p == 2:
            return (self.and_(a[0], b[0]),)
        if all(abs(x) == 1 for x in a):
            a, b = b, a
        result = self.zero
        for i, bit in enumerate(b):
            if bit != self.false:
                result = self.add(result, tuple(self.and_(bit, x) for x in a))
            if i + 1 < len(b) and any(x != self.false for x in b[i+1:]):
                a = self.add(a, a)
        return result

    def dot(self, terms):
        acc = self.zero
        for a, b in terms:
            acc = self.add(acc, self.mul(a, b))
        return acc

    def matrix(self, rows, cols):
        return [[self.fieldvar() for _ in range(cols)] for _ in range(rows)]

    def invertible(self, matrix):
        s = len(matrix)
        inverse = self.matrix(s, s)
        for i in range(s):
            for j in range(s):
                self.eq(self.dot((matrix[i][h], inverse[h][j]) for h in range(s)),
                        self.constant(int(i == j)))


def construct(p, m, n, k, a, b, circuit):
    c = circuit
    left, right, mix = c.matrix(m, m), c.matrix(n, n), c.matrix(k, k)
    for t in (left, right, mix):
        c.invertible(t)
    for h in range(k):
        inter = [[c.dot((left[i][s], c.constant(a[h][s][j])) for s in range(m))
                  for j in range(n)] for i in range(m)]
        for i in range(m):
            for j in range(n):
                c.eq(c.dot((inter[i][s], right[s][j]) for s in range(n)),
                     c.dot((mix[h][s], c.constant(b[s][i][j])) for s in range(k)))
    return left, right, mix


def solve(path, solver, timeout, clause_limit):
    start = perf_counter()
    p, m, n, k, a, b = read_pair(path)
    after_read = perf_counter()
    result = {"case": path.name, "format": [p, m, n, k], "backend": "CaDiCaL"}
    result["read_ms"] = 1000 * (after_read - start)
    with tempfile.TemporaryDirectory(prefix="mce-sat-") as folder:
        filename = Path(folder) / "instance.cnf"
        with filename.open("w+", encoding="ascii", newline="\n") as f:
            f.write(" " * 96 + "\n")
            c = Circuit(f, p, clause_limit)
            try:
                variables = construct(p, m, n, k, a, b, c)
            except ConstructionLimit:
                result.update(result="construction_limit", clauses=c.clauses,
                              build_ms=1000 * (perf_counter() - after_read),
                              total_ms=1000 * (perf_counter() - start))
                return result
            f.seek(0)
            header = f"p cnf {c.variables} {c.clauses}"
            f.write(header + " " * (96 - len(header)))
        after_build = perf_counter()
        result.update(variables=c.variables, clauses=c.clauses, build_ms=1000 * (after_build - after_read))
        try:
            run = subprocess.run([str(solver), "-q", str(filename)],
                                 capture_output=True, text=True, timeout=timeout)
            after_search = perf_counter()
            if run.returncode == 10:
                status = "yes"
            elif run.returncode == 20:
                status = "no"
            else:
                status = "error"
                result["returncode"] = run.returncode
        except subprocess.TimeoutExpired:
            status = "timeout"
            after_search = perf_counter()
        result["result"] = status
        result["search_ms"] = 1000 * (after_search - after_build)
        if status == "yes":
            truth = {int(lit) for row in run.stdout.splitlines() if row.startswith("v ")
                     for lit in row.split()[1:]}
            if any(x not in truth and -x not in truth for x in range(1, c.variables + 1)):
                raise AssertionError("Incomplete SAT model")
            matrices = [[[sum(1 << j for j, x in enumerate(bits) if x in truth)
                          for bits in row] for row in matrix] for matrix in variables]
            if not verify(p, m, n, k, a, b, *matrices):
                raise AssertionError("Witness failed independent verification")
            result.update(zip(("left", "right", "mixing"), matrices))
        result["verify_ms"] = 1000 * (perf_counter() - after_search)
    result["total_ms"] = 1000 * (perf_counter() - start)
    return result


def main():
    args = argparse.ArgumentParser(description=__doc__)
    args.add_argument("cases", nargs="+", type=Path)
    args.add_argument("--cadical", type=Path, required=True)
    args.add_argument("--timeout", type=float, default=3)
    args.add_argument("--clause-limit", type=int, default=3_000_000)
    p = args.parse_args()
    if min(p.timeout, p.clause_limit) <= 0:
        args.error("Limits must be positive")
    for path in p.cases:
        print(json.dumps(solve(path, p.cadical.resolve(), p.timeout, p.clause_limit)), flush=True)


if __name__ == "__main__":
    main()
