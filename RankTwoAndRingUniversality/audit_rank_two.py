from itertools import product


class PartialMatrix:
    def __init__(self, prime):
        self.prime = prime
        self.rows = {}
        self.columns = {}
        self.entries = {}
        self.row("e1", (1, 0))
        self.row("e2", (0, 1))
        self.column("e1", (1, 0))
        self.column("e2", (0, 1))
        for i, j in product((1, 2), repeat=2):
            self.pin(f"e{i}", f"e{j}", int(i == j))

    def row(self, label, coordinates):
        assert label not in self.rows
        self.rows[label] = coordinates

    def column(self, label, coordinates):
        assert label not in self.columns
        self.columns[label] = coordinates

    def pin(self, row, column, value):
        assert value in (0, 1) and row in self.rows and column in self.columns
        assert (row, column) not in self.entries, (row, column, value)
        self.entries[row, column] = value

    def valid(self):
        return all(
            sum(a * b for a, b in zip(self.rows[row], self.columns[column])) % self.prime == value
            for (row, column), value in self.entries.items()
        )

    def fixed(self):
        for name, value in (("ones", (1, 1)), ("neg2", (1, -1)), ("neg1", (-1, 1))):
            self.row(name, value)
            self.column(name, value)
        self.pin("ones", "e1", 1)
        self.pin("ones", "e2", 1)
        self.pin("e1", "ones", 1)
        self.pin("e2", "ones", 1)
        self.pin("neg2", "e1", 1)
        self.pin("neg2", "ones", 0)
        self.pin("e1", "neg2", 1)
        self.pin("ones", "neg2", 0)
        self.pin("neg1", "e2", 1)
        self.pin("neg1", "ones", 0)
        self.pin("e2", "neg1", 1)
        self.pin("ones", "neg1", 0)
        self.row("axisneg1", (-1, 0))
        self.row("axisneg2", (0, -1))
        self.pin("axisneg1", "e2", 0)
        self.pin("axisneg1", "neg1", 1)
        self.pin("axisneg2", "e1", 0)
        self.pin("axisneg2", "neg2", 1)

    def scalar(self, label, value):
        inverse = pow(value, -1, self.prime)
        names = {letter: f"{label}:{letter}" for letter in "RDUVKQLP"}
        for letter, coordinates in (("R", (value, 1)), ("D", (value, value)),
                                    ("Q", (0, inverse)), ("P", (inverse, 0))):
            self.row(names[letter], coordinates)
        for letter, coordinates in (("U", (inverse, 0)), ("V", (0, inverse)),
                                    ("K", (-1, value)), ("L", (value, value))):
            self.column(names[letter], coordinates)
        for row, column, pin in (
            ("R", "e2", 1), ("e2", "U", 0), ("R", "U", 1),
            ("D", "neg2", 0), ("D", "U", 1), ("e1", "V", 0), ("D", "V", 1),
            ("axisneg1", "K", 1), ("R", "K", 0), ("Q", "e1", 0), ("Q", "K", 1),
            ("neg2", "L", 0), ("Q", "L", 1), ("P", "e2", 0), ("P", "L", 1),
        ):
            self.pin(names.get(row, row), names.get(column, column), pin)

    def multiply(self, label, variable_names, values):
        x, y, z = variable_names
        a, b, c = values
        row, col = f"{label}:r", f"{label}:c"
        self.row(row, (a, c))
        self.column(col, (b, -1))
        self.pin(row, f"{x}:U", 1)
        self.pin(row, f"{z}:V", 1)
        self.pin(f"{y}:P", col, 1)
        self.pin("axisneg2", col, 1)
        self.pin(row, col, 0)

    def add(self, label, variable_names, values):
        x, y, z = variable_names
        a, b, c = values
        u, v = f"{label}:u", f"{label}:v"
        d, e = a * pow(c, -1, self.prime) % self.prime, b * pow(c, -1, self.prime) % self.prime
        self.scalar(u, d)
        self.scalar(v, e)
        self.multiply(f"{label}:mu", (u, z, x), (d, c, a))
        self.multiply(f"{label}:mv", (v, z, y), (e, c, b))
        row = f"{label}:sum"
        self.row(row, (d, e))
        self.pin(row, f"{u}:U", 1)
        self.pin(row, f"{v}:V", 1)
        self.pin(row, "ones", 1)


def copy_solutions(x, p):
    residues = range(p)
    for u in residues:
        if x * u % p != 1:
            continue
        for d in residues:
            if d * u % p != 1:
                continue
            for v, k, w, l, s in product(residues, repeat=5):
                if d * v % p == 1 and (k - x) % p == 0 and w * k % p == 1 and w * l % p == 1 and s * l % p == 1:
                    yield u, d, v, k, w, l, s


def finite_coloring_pair(u, v, vectors, p):
    def dot(x, y):
        return (x[0] * y[0] + x[1] * y[1]) % p
    columns_u = [c for c in vectors if dot(u, c) == 0]
    columns_v = [c for c in vectors if dot(v, c) == 0]
    wanted = (u[0] * v[1] - u[1] * v[0]) % p != 0
    for c, d in product(columns_u, columns_v):
        assert any(dot(t, c) == 0 and dot(t, d) == 1 for t in vectors) == wanted


def main():
    copy_count = 0
    arithmetic_count = 0
    coloring_count = 0
    for p in (2, 3, 5, 7):
        for x in range(p):
            solutions = list(copy_solutions(x, p))
            if not x:
                assert not solutions
            else:
                inv = pow(x, -1, p)
                assert solutions == [(inv, x, inv, x, inv, x, inv)]
            copy_count += 1
        for values in product(range(1, p), repeat=3):
            x, y, z = values
            for method, expected in (
                ("multiply", (x * y - z) % p == 0),
                ("add", (x + y - z) % p == 0),
            ):
                matrix = PartialMatrix(p)
                matrix.fixed()
                labels = tuple(str(value) for value in values)
                for label, value in dict(zip(labels, values)).items():
                    matrix.scalar(label, value)
                getattr(matrix, method)("gate", labels, values)
                assert matrix.valid() == expected, (p, values, method)
                arithmetic_count += 1
        vectors = list(product(range(p), repeat=2))[1:]
        for u, v in product(vectors, repeat=2):
            finite_coloring_pair(u, v, vectors, p)
            coloring_count += 1
    print(f"{copy_count} scalar-copy, {arithmetic_count} gate, {coloring_count} coloring-pair checks passed over F2/F3/F5/F7")
    print("All checked explicit partial matrices used only pinned 0/1 and no duplicate prescribed coordinates.")


if __name__ == "__main__":
    main()

