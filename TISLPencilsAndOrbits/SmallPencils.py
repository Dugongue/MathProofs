"""All F3 tensors of shape (2,2,2) as a finite audit of the pencil argument."""
from collections import deque


def apply(tensor, axis, matrix):
    stride = (4, 2, 1)[axis]
    out = list(tensor)
    for i in range(8):
        if not i & stride:
            x, y = tensor[i], tensor[i + stride]
            out[i] = (matrix[0]*x + matrix[1]*y) % 3
            out[i + stride] = (matrix[2]*x + matrix[3]*y) % 3
    return tuple(out)


def orbit(base):
    # Transvections generate SL_2; a reflection supplies the other GL_2 coset.
    generators = ((1, 1, 0, 1), (1, 0, 1, 1), (2, 0, 0, 1))
    todo = deque([(base, 0)])
    profiles = {base: {0}}
    while todo:
        tensor, profile = todo.popleft()
        for axis in range(3):
            for j, generator in enumerate(generators):
                new = apply(tensor, axis, generator)
                sign = profile ^ ((1 << axis) if j == 2 else 0)
                values = profiles.setdefault(new, set())
                if sign not in values:
                    values.add(sign)
                    todo.append((new, sign))
    return profiles


all_signs = set(range(8))
cases = {
    "zero": ((0,)*8, all_signs),
    "rank one": ((1,0,0,0,0,0,0,0), all_signs),
    # If one leg is a line, the other two transport a full-rank matrix.
    "slice line": ((1,0,0,1,0,0,0,0), {0,1,6,7}),
    "row line": ((1,0,0,0,0,1,0,0), {0,2,5,7}),
    "column line": ((1,0,0,0,0,0,1,0), {0,3,4,7}),
    # The one length-two block leaves just the common sign on all three legs.
    "repeated root": ((1,0,0,1,0,1,0,0), {0,7}),
    # Exchanging the two roots, or using field conjugation, supplies odd parity.
    "split": ((1,0,0,0,0,0,0,1), all_signs),
    "nonsplit": ((1,0,0,1,0,2,1,0), all_signs),
}


def main():
    covered = set()
    for label, (tensor, predicted) in cases.items():
        profiles = orbit(tensor)
        assert profiles[tensor] == predicted, (label, profiles[tensor], predicted)
        assert covered.isdisjoint(profiles), label
        for values in profiles.values():
            offset = next(iter(values))
            assert values == {offset ^ s for s in predicted}
        covered.update(profiles)
    assert len(covered) == 3**8
    print("Verified all 6,561 ternary 2-by-2-by-2 tensors and eight template stabilizer profiles.")


if __name__ == "__main__":
    main()
