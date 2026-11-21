"""Enumerate graded maps and the full graded-identity kernel in two small algebras."""
from itertools import product


def check(concise):
    names = ("one", "x", "z", "w", "dual", "z2", "e", "s") if concise else (
        "one", "r", "z", "w", "z2", "e", "s")
    basis = {name: 1 << i for i, name in enumerate(names)}
    table = {}
    for name in names:
        table[(basis["one"], basis[name])] = basis[name]
    for x, y, z in [("z", "z", "z2"), ("z", "z2", "s"), ("z", "w", "e")]:
        table[(basis[x], basis[y])] = basis[z]
    if concise:
        table[(basis["x"], basis["x"])] = basis["dual"]
        table[(basis["dual"], basis["x"])] = basis["s"]
    table.update({(y, x): z for (x, y), z in tuple(table.items())})

    def multiply(u, v):
        result = 0
        while u:
            x = u & -u
            u ^= x
            t = v
            while t:
                y = t & -t
                t ^= y
                result ^= table.get((x, y), 0)
        return result

    generators = names[1:4]
    higher = names[4:]

    def span(vectors):
        sums = {0}
        for v in vectors:
            sums |= {v ^ s for s in sums}
        return sums

    def homomorphism(images):
        mapped = {"one": 1, **dict(zip(generators, images))}
        z, w = mapped["z"], mapped["w"]
        mapped["z2"] = multiply(z, z)
        mapped["e"] = multiply(z, w)
        mapped["s"] = multiply(z, mapped["z2"])
        if concise:
            mapped["dual"] = multiply(mapped["x"], mapped["x"])
        if len(span(mapped.values())) != 2 ** len(names):
            return False
        for x in names:
            for y in names:
                target = table.get((basis[x], basis[y]), 0)
                image = mapped[names[target.bit_length()-1]] if target else 0
                if multiply(mapped[x], mapped[y]) != image:
                    return False
        return True

    grade_one = span(basis[x] for x in generators) - {0}
    ungraded_corrections = span(basis[x] for x in higher)
    graded = sum(homomorphism(images) for images in product(grade_one, repeat=3))
    kernel = sum(homomorphism(tuple(basis[x] ^ y for x, y in zip(generators, shifts)))
                 for shifts in product(ungraded_corrections, repeat=3))
    expected = (2, 1024) if concise else (8, 256)
    assert (graded, kernel) == expected
    print(f"Over F2 with concise dimension {int(concise)}: {graded} graded maps, "
          f"{kernel} graded-identity maps, {graded * kernel} automorphisms.")


def main():
    check(True)
    check(False)
    cubes = {a**3 % 7 for a in range(1, 7)}
    assert cubes == {1, 6}
    assert all(2*s**3 % 7 != a**3 % 7 for s, a in product(range(1, 7), repeat=2))
    print("The one-variable F7 pair is projectively equivalent and has no exact transport.")


if __name__ == "__main__":
    main()
