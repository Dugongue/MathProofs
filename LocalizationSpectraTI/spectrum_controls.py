"""Exact controls for independent units and all four-variable monotone spectra."""

from itertools import product
import json


def crt(residues):
    modulus, value = 1, 0
    for q, a in residues:
        delta = (a-value) * pow(modulus, -1, q) % q
        value += modulus * delta
        modulus *= q
    return value


def unit_checks():
    pin, data = 5, (7, 11, 13, 17)
    factors = []
    for i in range(len(data)):
        residues = [(3, -1), (pin, -1)]
        residues.extend((q, 1 if i == j else -1) for j, q in enumerate(data))
        factors.append(crt(residues))
    assert len(set(factors)) == len(data)
    tests = 0
    for selected in range(1 << len(data)):
        indices = [i for i in range(len(data)) if selected & (1 << i)]
        seen = [set() for _ in data]
        for exponents in product((-1, 0, 1), repeat=len(indices)):
            for j, q in enumerate(data):
                value = 1
                for i, exponent in zip(indices, exponents):
                    assert (-factors[i]) % pin == (-factors[i]) % 3 == 1
                    value = value * pow(-factors[i], exponent, q) % q
                seen[j].add(value)
                tests += 1
        for j, q in enumerate(data):
            expected = {1, q-1} if j in indices else {1}
            assert seen[j] == expected
    return {"selection_subsets": 1 << len(data), "crt_unit_evaluations": tests}


def span_contains(columns, b):
    echelon = {}
    for v in columns:
        while v:
            k = v.bit_length()
            if k not in echelon:
                echelon[k] = v
                break
            v ^= echelon[k]
    while b:
        k = b.bit_length()
        if k not in echelon:
            return False
        b ^= echelon[k]
    return True


def compile_antichain(minimal):
    if 0 in minimal:
        return [], 0
    endpoints, vertices, edges = 3, 2, []
    for chosen in minimal:
        labels = [i for i in range(4) if chosen & (1 << i)]
        u = 0
        for j, label in enumerate(labels):
            if j == len(labels)-1:
                v = 1
            else:
                v = vertices
                vertices += 1
            edges.append(((1 << u) ^ (1 << v), label))
            u = v
    return edges, endpoints


def span_checks():
    covers = [(s, s | (1 << i)) for s in range(16) for i in range(4)
              if s & (1 << i) == 0]
    total, values = 0, 0
    for encoding in range(1 << 16):
        def accepted(s):
            return bool(encoding & (1 << s))

        if any(accepted(s) and not accepted(t) for s, t in covers):
            continue
        minimal = [s for s in range(16) if accepted(s) and
                   all(not accepted(s ^ (1 << i)) for i in range(4) if s & (1 << i))]
        edges, b = compile_antichain(minimal)
        for s in range(16):
            cols = [v for v, label in edges if s & (1 << label)]
            assert span_contains(cols, b) == accepted(s)
            # The extra column is disabled in the listed global choices and
            # enabled at every prime localization.
            assert span_contains(cols + [b], b)
            values += 1
        total += 1
    assert total == 168
    return {"upward_closed_families_on_four_bits": total, "family_subset_checks": values}


def arithmetic_jet_checks():
    scalar = {}
    for k in (1, 2):
        observed, precision = 3**k, 3**(k+1)
        units = [u for u in range(precision) if u % 3]
        for target in (1, 2):
            for localized in (False, True):
                choices = units if localized else (1,)
                images = set()
                for a, b, c in product(choices, repeat=3):
                    numerator = c-target*a*b
                    if numerator % 3 == 0:
                        images.add((a % observed, b % observed, c % observed,
                                    (numerator//3) % observed))
                expected = (12 if k == 1 else 324) if localized else int(target == 1)
                assert len(images) == expected
                scalar[f"{k}-{target}-{int(localized)}"] = len(images)

    rank_one = {}
    for localized in (False, True):
        units = (1, 2, 4, 5, 7, 8) if localized else (1,)
        images = set()
        for a, b, c, d in product(range(9), repeat=4):
            det = (a*d-b*c) % 9
            determinant_allowed = bool(det % 3) if localized else det == 1
            if not determinant_allowed:
                continue
            for y, z in product(units, repeat=2):
                left, right = z-a*y, -b*y
                if left % 3 == right % 3 == 0:
                    images.add(tuple(x % 3 for x in (a, b, c, d, y, z, left//3, right//3)))
        assert len(images) == (216 if localized else 27)
        rank_one[str(int(localized))] = len(images)
    return {"scalar_congruence_images": scalar, "rank_one_congruence_images": rank_one}


if __name__ == "__main__":
    print(json.dumps({**unit_checks(), **span_checks(), **arithmetic_jet_checks()}, indent=2))
