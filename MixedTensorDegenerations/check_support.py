from itertools import product
from random import Random


def dot(left, right, p):
    return sum(a * b for a, b in zip(left, right)) % p


def solve(rows, target, size, p):
    augmented = [list(row) + [value] for row, value in zip(rows, target)]
    pivots = []
    for j in range(size):
        pivot = next((i for i in range(len(pivots), len(augmented)) if augmented[i][j] % p), None)
        if pivot is None:
            continue
        i = len(pivots)
        augmented[i], augmented[pivot] = augmented[pivot], augmented[i]
        inverse = pow(augmented[i][j] % p, -1, p)
        augmented[i] = [(v * inverse) % p for v in augmented[i]]
        for k, row in enumerate(augmented):
            if k != i and row[j]:
                factor = row[j]
                augmented[k] = [(x - y * factor) % p for x, y in zip(row, augmented[i])]
        pivots.append(j)
    if any(row[-1] and not any(row[:-1]) for row in augmented):
        return None
    answer = [0] * size
    for i, j in enumerate(pivots):
        answer[j] = augmented[i][-1]
    return tuple(answer)


def standard(n):
    return [tuple(int(i == j) for i in range(n)) for j in range(n)]


def lincomb(columns, coefficients, n, p):
    return tuple(sum(v[i] * c for c, v in zip(coefficients, columns)) % p for i in range(n))


def coordinates(columns, target, p):
    return solve(list(zip(*columns)) if columns else [()] * len(target), target, len(columns), p)


def extend(prefix, candidates, p):
    basis = list(prefix)
    for v in candidates:
        if coordinates(basis, v, p) is None:
            basis.append(v)
    return basis


def extend_pair(primal, dual, mapped_primal, mapped_dual, n, p):
    quotient_columns = [tuple(dot(u, v, p) for u in dual) for v in primal]
    quotient_basis = []
    lifts = []
    target_lifts = []
    kernel_basis = []
    target_kernel_basis = []
    for quotient, v, w in zip(quotient_columns, primal, mapped_primal):
        coefficients = coordinates(quotient_basis, quotient, p)
        if coefficients is None:
            quotient_basis.append(quotient)
            lifts.append(v)
            target_lifts.append(w)
        else:
            offset = lincomb(lifts, coefficients, n, p)
            target_offset = lincomb(target_lifts, coefficients, n, p)
            kernel_basis.append(tuple((a - b) % p for a, b in zip(v, offset)))
            target_kernel_basis.append(tuple((a - b) % p for a, b in zip(w, target_offset)))
    for quotient in extend(quotient_basis, standard(len(dual)), p)[len(quotient_basis):]:
        lifts.append(solve(dual, quotient, n, p))
        target_lifts.append(solve(mapped_dual, quotient, n, p))

    def kernel_span(forms):
        # These projection differences span the kernel without listing the field.
        lifts_of_coordinates = [solve(forms, e, n, p) for e in standard(len(forms))]
        for v in standard(n):
            coefficients = tuple(dot(u, v, p) for u in forms)
            offset = lincomb(lifts_of_coordinates, coefficients, n, p)
            yield tuple((a - b) % p for a, b in zip(v, offset))

    basis = extend(kernel_basis, kernel_span(dual), p) + lifts
    target_basis = extend(target_kernel_basis, kernel_span(mapped_dual), p) + target_lifts
    assert len(basis) == len(target_basis) == n
    return [lincomb(target_basis, coordinates(basis, e, p), n, p) for e in standard(n)]


def random_basis(n, p, rng):
    basis = []
    while len(basis) != n:
        proposal = tuple(rng.randrange(p) for _ in range(n))
        basis = extend(basis, [proposal], p)
    return basis


def exercise_pairing():
    rng = Random(7429)
    checked = 0
    for p, n in product((2, 3, 5), range(1, 6)):
        for a, b in product(range(n + 1), repeat=2):
            for _ in range(2):
                primal = random_basis(n, p, rng)[:a]
                dual = random_basis(n, p, rng)[:b]
                chosen = random_basis(n, p, rng)
                mapped_primal = [lincomb(chosen, v, n, p) for v in primal]
                mapped_dual = [solve(chosen, u, n, p) for u in dual]
                witness = extend_pair(primal, dual, mapped_primal, mapped_dual, n, p)
                assert extend([], witness, p) == witness
                assert [lincomb(witness, v, n, p) for v in primal] == mapped_primal
                assert [solve(witness, u, n, p) for u in dual] == mapped_dual
                checked += 1
    return checked


class Cell:
    """The algebra over F3 with each of its quadratic factors satisfying i^2=-1."""

    def __init__(self, labels):
        self.labels = labels
        self.masks = [mask for mask in range(1 << len(labels))
                      if all(not(mask >> j & 1) or label for j, label in enumerate(labels))]
        self.index = {mask: j for j, mask in enumerate(self.masks)}
        self.basis = standard(len(self.masks))
        self.one = self.basis[0]

    def multiply(self, a, b):
        result = [0] * len(self.masks)
        for i, x in enumerate(a):
            for j, y in enumerate(b):
                sign = (-1) ** ((self.masks[i] & self.masks[j]).bit_count())
                result[self.index[self.masks[i] ^ self.masks[j]]] += sign * x * y
        return tuple(value % 3 for value in result)

    def inverse(self, a):
        columns = [self.multiply(a, e) for e in self.basis]
        return solve(list(zip(*columns)), self.one, len(self.masks), 3)

    def frobenius(self, a, position):
        return tuple((-x if mask >> position & 1 else x) % 3
                     for mask, x in zip(self.masks, a))

    def insert(self, a, position):
        result = [0] * len(self.masks)
        for j, x in enumerate(a):
            result[self.index[j << position]] = x
        return tuple(result)

    def coefficient(self, a, position):
        bit = int(bool(self.labels[position])) << position
        for mask in self.masks:
            if not mask & bit:
                candidate = ((a[self.index[mask]], a[self.index[mask | bit]]) if bit
                             else (a[self.index[mask]],))
                if any(candidate):
                    return candidate
        raise AssertionError("zero ratio")


SIGNATURES = (((1, -1), (0, 1)), ((0, 1), (0, -1), (1, 1)), ((0, -1), (1, -1)))
FIELDS = {label: Cell((label,)) for label in (0, 1)}
UNITS = {label: [x for x in product(range(3), repeat=len(field.masks)) if any(x)]
         for label, field in FIELDS.items()}
CELLS = {(r, labels): Cell(labels) for r, word in enumerate(SIGNATURES)
         for labels in product((0, 1), repeat=len(word))}
VARIABLES = list(product((0, 1), repeat=2))


def field_divide(a, b, field):
    return field.multiply(a, field.inverse(b))


def act(data, multipliers):
    output = {}
    for key, x in data.items():
        r, labels = key
        cell = CELLS[key]
        y = x
        for j, ((s, sign), label) in enumerate(zip(SIGNATURES[r], labels)):
            a = multipliers[(s, label)]
            if sign < 0:
                a = FIELDS[label].inverse(a)
            y = cell.multiply(y, cell.insert(a, j))
        output[key] = y
    return output


def normalize_frobenius(data):
    multipliers = {}
    for s, label in VARIABLES:
        field = FIELDS[label]
        multipliers[(s, label)] = field.one
        hits = [(key, j, sign) for key, x in sorted(data.items()) if any(x)
                for j, ((name, sign), part) in enumerate(zip(SIGNATURES[key[0]], key[1]))
                if name == s and part == label]
        if not hits:
            continue
        key, position, sign = hits[0]
        cell = CELLS[key]
        x = data[key]
        ratio = field_divide(cell.frobenius(x, position), x, cell)
        c = cell.coefficient(ratio, position)
        norm = field.multiply(c, field.frobenius(c, 0)) if label else c
        section = next(z for z in UNITS[label]
                       if (field.multiply(z, field.frobenius(z, 0)) if label else z) == norm)
        target = field_divide(section, c, field)
        if sign < 0:
            target = field.inverse(target)
        multipliers[(s, label)] = next(z for z in UNITS[label]
                                       if field_divide(field.frobenius(z, 0), z, field) == target)
    return act(data, multipliers)


def residual_canon(data):
    keys = [key for key in sorted(data) if any(data[key])]
    first = [next(entry for entry in data[key] if entry) - 1 for key in keys]
    incidence = [[sum(sign for (name, sign), label in zip(SIGNATURES[key[0]], key[1])
                      if (name, label) == variable) for variable in VARIABLES] for key in keys]

    def result_for(word):
        return tuple((a + dot(row, word, 2)) % 2 for a, row in zip(first, incidence))

    # Exhaustive independent finite replay of the congruence interface.
    candidates = list(product((0, 1), repeat=len(VARIABLES)))
    shift = min(candidates, key=result_for)
    multipliers = {variable: (1 + t,) + (0,) * variable[1] for variable, t in zip(VARIABLES, shift)}
    return act(data, multipliers)


def canonical(data):
    return residual_canon(normalize_frobenius(data))


def sample_data(rng):
    data = {}
    for key, cell in CELLS.items():
        if rng.randrange(3) == 0:
            data[key] = (0,) * len(cell.masks)
            continue
        while True:
            candidate = tuple(rng.randrange(3) for _ in cell.masks)
            if cell.inverse(candidate) is not None:
                data[key] = candidate
                break
    return data


def exercise_missing_cells():
    rng = Random(7430)
    split = Cell((1, 1))
    nonunit = (1, 0, 0, 1)
    assert any(nonunit) and split.inverse(nonunit) is None
    total = 0
    samples = [sample_data(rng) for _ in range(6)]
    for sample in samples:
        assert any(not any(v) for v in sample.values())
        assert any(any(v) for v in sample.values())
        reference = canonical(sample)
        assert canonical(reference) == reference
        for _ in range(12):
            multipliers = {var: rng.choice(UNITS[var[1]]) for var in VARIABLES}
            assert canonical(act(sample, multipliers)) == reference
            total += 1
        count = 0
        # Search the full action group independently to certify orbit membership.
        orbit_match = False
        for multipliers in product(*(UNITS[var[1]] for var in VARIABLES)):
            count += 1
            if act(sample, dict(zip(VARIABLES, multipliers))) == reference:
                orbit_match = True
        assert count == 256 and orbit_match
    return total


if __name__ == "__main__":
    print(f"Ambient pairing extensions verified: {exercise_pairing()}")
    print(f"Missing-cell signed normalization transforms checked: {exercise_missing_cells()}")
    print("Six independent 256-element orbit replays and a nonzero nonunit rejection passed.")
