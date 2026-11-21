"""Exact finite checks for the affine chart on the one-variable algebra."""
from itertools import product
from math import comb


def instance(modulus, f):
    degree = 4
    one = (0, 0)
    x, t = (1, 0), (0, 1)
    z, w = "z1", "w"
    basis = [(i, j) for total in range(degree + 1)
             for i in range(total + 1) for j in [total - i]]
    basis += ["z1", "z2", "z3", "w", "mx", "mt", "e"]

    def on_basis(a, b):
        if a == one:
            return {b: 1}
        if b == one:
            return {a: 1}
        if isinstance(a, tuple) and isinstance(b, tuple):
            out = (a[0] + b[0], a[1] + b[1])
            return {out: 1} if sum(out) <= degree else {}
        if isinstance(a, str) and isinstance(b, str) and a[0] == b[0] == "z":
            k = int(a[1]) + int(b[1])
            if k == degree:
                return {(i, degree-i): v for i, v in f.items() if v}
            if k < degree:
                return {f"z{k}": 1}
        if a == w or b == w:
            other = b if a == w else a
            outputs = {x: "mx", t: "mt", z: "mt", w: "e"}
            if other in outputs:
                return {outputs[other]: 1}
        return {}

    def mul(a, b):
        out = {}
        for x0, x1 in a.items():
            for y0, y1 in b.items():
                for z0, coefficient in on_basis(x0, y0).items():
                    out[z0] = (out.get(z0, 0) + x1*y1*coefficient) % modulus
        return {k: c for k, c in out.items() if c}

    return basis, on_basis, mul


def translate(value, alpha, beta, modulus):
    out = {}
    for symbol, coefficient in value.items():
        if isinstance(symbol, tuple):
            i, j = symbol
            terms = {(k, i+j-k): comb(i, k)*alpha**k*beta**(i-k)
                     for k in range(i+1)}
        elif symbol == "mx":
            terms = {"mx": alpha, "mt": beta}
        else:
            terms = {symbol: 1}
        for target, scalar in terms.items():
            out[target] = (out.get(target, 0) + coefficient*scalar) % modulus
    return {k: c for k, c in out.items() if c}


def main():
    for p in (2, 3, 4):
        basis, prod, mul = instance(p, {3: 1, 1: 1})
        for a, b, c in product(basis, repeat=3):
            assert mul(prod(a, b), {c: 1}) == mul({a: 1}, prod(b, c))
        x, t = (1, 0), (0, 1)
        degree1 = [x, t, "z1", "w"]
        two = [(2, 0), (1, 1), (0, 2), "z2", "mx", "mt", "e"]
        testers = [dict(zip(degree1, values)) for values in product(range(p), repeat=4)]
        for v in testers:
            drop = all(not (set(mul(v, {u: 1})) - {"mx", "mt", "e"}) for u in degree1)
            assert drop == (all(v[u] == 0 for u in degree1[:-1]))
            annihilates_w = not mul(v, {"w": 1})
            assert annihilates_w == (v[x] == v["w"] == 0 and (v[t]+v["z1"]) % p == 0)
        for a in two:
            assert all(not prod(a, u) for u in degree1) == (a in {"mx", "mt", "e"})

    old, source, _ = instance(4, {3: 1, 1: 1})
    _, _, target_mul = instance(4, {3: 1, 2: 2, 1: 1, 0: 2})
    for a, b in product(old, repeat=2):
        assert translate(source(a, b), 1, 2, 4) == target_mul(
            translate({a: 1}, 1, 2, 4), translate({b: 1}, 1, 2, 4))
    print("All basis triples and chart-kernel checks passed over F2, F3, and Z/4.")
    print("Every basis-pair product preserved by the translation x -> x + 2 over Z/4.")


if __name__ == "__main__":
    main()
