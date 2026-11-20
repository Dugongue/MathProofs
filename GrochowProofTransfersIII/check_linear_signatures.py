"""Exact coordinate checks for mixed tensor words split into three blocks."""
from itertools import product
import random


def inverse_dual(g, p):
    a, b, c, d = (x for row in g for x in row)
    scale = pow((a*d-b*c) % p, -1, p)
    return [[d*scale % p, -c*scale % p], [-b*scale % p, a*scale % p]]


def compose(a, b, p):
    return [[sum(x*y for x, y in zip(row, col)) % p for col in zip(*b)]
            for row in a]


def kron(a, b, p):
    return [[x*y % p for x in ar for y in br] for ar in a for br in b]


def power_word(word, g, gd, p):
    result = [[1]]
    for letter in word:
        result = kron(result, g if letter == "+" else gd, p)
    return result


def word_action(word, original, g, gd, p):
    coords = list(product(range(2), repeat=len(word)))
    out = {idx: original[j] for j, idx in enumerate(coords)}
    for k, letter in enumerate(word):
        mat = g if letter == "+" else gd
        out = {idx: sum(mat[idx[k]][j]*out[idx[:k]+(j,)+idx[k+1:]] for j in range(2)) % p
               for idx in coords}
    return [out[idx] for idx in coords]


def group_word(word):
    n, extra = divmod(len(word), 3)
    sizes = [n + (i < extra) for i in range(3)]
    a, b, _ = sizes
    return (word[:a], word[a:a+b], word[a+b:])


def flip(word):
    return word.translate(str.maketrans("+-", "-+"))


def transposed(a):
    return [list(col) for col in zip(*a)]


def check_tensor(word, data, g, gd, p):
    blocks = group_word(word)
    maps = [power_word(block, g, gd, p) for block in blocks]
    full = kron(kron(maps[0], maps[1], p), maps[2], p)
    transformed = word_action(word, data, g, gd, p)
    assert [row[0] for row in compose(full, [[x] for x in data], p)] == transformed
    a, b, c = [len(m) for m in maps]
    dual = [power_word(flip(block), g, gd, p) for block in blocks[:2]]
    # Viewing the grouped tensor as a bilinear map pairs against P*, Q*.
    # Check all pairs of covector basis elements and every output coordinate.
    source = [data[i*c:(i+1)*c] for i in range(a*b)]
    target = [transformed[i*c:(i+1)*c] for i in range(a*b)]
    by_new_input = compose(transposed(kron(*dual, p)), target, p)
    by_new_output = compose(source, transposed(maps[2]), p)
    assert by_new_input == by_new_output


def check_operation(word, data, g, gd, p):
    assert word[-1] == "+"
    changed = word_action(word, data, g, gd, p)
    domain = power_word(flip(word[:-1]), g, gd, p)
    old = [data[i:i+2] for i in range(0, len(data), 2)]
    new = [changed[i:i+2] for i in range(0, len(changed), 2)]
    assert compose(transposed(domain), new, p) == compose(old, transposed(g), p)
    check_tensor(word, data, g, gd, p)


def main():
    rng = random.Random(190700309)
    checked = 0
    for p in (2, 3, 5):
        matrices = ([[a, b], [c, d]] for a, b, c, d in product(range(p), repeat=4)
                    if (a*d-b*c) % p)
        for g in matrices:
            gd = inverse_dual(g, p)
            assert compose(transposed(gd), g, p) == [[1, 0], [0, 1]]
            for word in ("", "+", "++-+", "+-++-", "++--+-", "----++"):
                data = [rng.randrange(p) for _ in range(2**len(word))]
                check_tensor(word, data, g, gd, p)
                checked += 1
            for word in ("+", "-+", "++-+", "-++-+", "-+--+"):
                data = [rng.randrange(p) for _ in range(2**len(word))]
                check_operation(word, data, g, gd, p)
                checked += 1
    print(f"Verified {checked} mixed tensor and operation cases over F2, F3 and F5.")


if __name__ == "__main__":
    main()
