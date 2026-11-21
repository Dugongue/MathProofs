from collections import defaultdict
from fractions import Fraction as Q
from itertools import permutations, product
from math import factorial, prod

D = 4
LETTERS = tuple(range(D))
HALF = Q(1, 2)
UNIFORM = Q(1, D)
EPSILON = Q(1, 512)
STATES = ((),) + tuple((a,) for a in LETTERS) + tuple(product(LETTERS, repeat=2))
INDEX = {state: i for i, state in enumerate(STATES)}
PI = tuple(Q(1, 3 * D ** len(state)) for state in STATES)


def contrast(i, a):
    return int(a == i) - int(a == 0)


def alternating(a, b, c):
    args = (a, b, c)
    coefficient = 0
    for perm in permutations(range(3)):
        sign = (-1) ** sum(perm[i] > perm[j] for i in range(3) for j in range(i + 1, 3))
        coefficient += sign * prod(contrast(perm[i] + 1, args[i]) for i in range(3))
    return coefficient


def source(scale):
    labels = []
    m = len(STATES)
    for a in LETTERS:
        matrix = [[Q(0)] * m for _ in STATES]
        for i, state in enumerate(STATES):
            if len(state) < 2:
                matrix[i][INDEX[state + (a,)]] = UNIFORM
            else:
                q = UNIFORM ** 3 + scale * EPSILON * alternating(*state, a)
                assert q > 0
                matrix[i][INDEX[()]] = D ** 2 * q
        labels.append(matrix)
    reset = [[[HALF * (x + UNIFORM * PI[j]) for j, x in enumerate(row)]
              for row in matrix] for matrix in labels]
    return labels, reset


def recode(matrices):
    # M = I + (e_1 - u/D)(e_1^* - e_0^*), with det(M) = 2.
    # M fixes u and b, scales the first contrast by two, and fixes the others.
    m = len(STATES)
    columns = tuple(tuple(int(a == b) + (int(a == 1) - UNIFORM) * contrast(1, b)
                          for a in LETTERS) for b in LETTERS)
    assert all(sum(col) == 1 for col in columns)
    assert all(sum(col[a] for col in columns) == 1 for a in LETTERS)
    assert min(min(col) for col in columns) < 0
    return [[[sum(columns[b][a] * matrices[a][i][j] for a in LETTERS)
              for j in range(m)] for i in range(m)] for b in LETTERS]


def row_times(row, matrix):
    return tuple(sum(x * y for x, y in zip(row, column) if x and y)
                 for column in zip(*matrix))


def word_table(matrices, limit=5):
    result = {}

    def visit(word, row):
        result[word] = sum(row)
        if len(word) < limit:
            for a in LETTERS:
                visit(word + (a,), row_times(row, matrices[a]))

    visit((), PI)
    return result


def sum_labeled_kernels(matrices):
    return tuple(tuple(sum(entries) for entries in zip(*rows))
                 for rows in zip(*matrices))


def by_reset_expansion(original, word):
    size = len(word)
    result = Q(0)
    for mask in product((False, True), repeat=size):
        parts = []
        start = 0
        for i, res in enumerate(mask):
            if res:
                parts.append(original[word[start:i]] * UNIFORM)
                start = i + 1
        parts.append(original[word[start:]])
        result += HALF ** size * prod(parts)
    return result


def histogram(word):
    return tuple(word.count(a) for a in LETTERS)


def check_coarsening(masses):
    for channel in product(range(3), repeat=D):
        observed = defaultdict(Q)
        for word, mass in masses.items():
            observed[tuple(channel[a] for a in word)] += mass
        marg = tuple(UNIFORM * channel.count(y) for y in range(3))
        assert all(mass == prod(marg[y] for y in word)
                   for word, mass in observed.items())


def main():
    a_original, a_reset = source(1)
    b_original, b_reset = source(2)
    _, iid_reset = source(0)
    assert sum_labeled_kernels(a_original) == sum_labeled_kernels(b_original)
    common = sum_labeled_kernels(a_reset)
    assert common == sum_labeled_kernels(b_reset) == sum_labeled_kernels(iid_reset)
    assert row_times(PI, common) == PI and all(sum(row) == 1 for row in common)
    assert all(x > 0 for matrix in a_reset + b_reset + iid_reset
               for row in matrix for x in row)

    a = word_table(a_reset)
    b = word_table(b_reset)
    iid = word_table(iid_reset)
    assert b == word_table(recode(a_reset))
    original = word_table(a_original)
    assert len(a) == 1365
    assert all(mass == by_reset_expansion(original, word) for word, mass in a.items())

    histograms = defaultdict(Q)
    long_pairs = defaultdict(Q)
    for word, mass in a.items():
        k = len(word)
        assert iid[word] == UNIFORM ** k
        if k <= 2:
            assert mass == iid[word]
        if k == 3:
            assert mass - iid[word] == EPSILON * alternating(*word) / 24
        if k == 5:
            for i in range(k):
                for j in range(i + 1, k):
                    long_pairs[i, j, word[i], word[j]] += mass
        if k < 5:
            for symbol in LETTERS:
                candidate = a[word + (symbol,)] / mass
                assert Q(3, 4) * UNIFORM <= candidate <= Q(5, 4) * UNIFORM
        histograms[histogram(word)] += mass
    assert len(long_pairs) == 160 and all(value == UNIFORM ** 2 for value in long_pairs.values())
    for counts, mass in histograms.items():
        k = sum(counts)
        assert mass == factorial(k) * UNIFORM ** k / prod(factorial(n) for n in counts)
    check_coarsening(a)
    assert a[(1, 2, 3)] != iid[(1, 2, 3)]  # The four-symbol identity channel detects D.
    print("1,365 exact word and reset identities through length 5, 126 histogram masses, "
          "160 pair marginals, all 81 deterministic ternary channels, "
          "and the signed recoding and four-output controls passed.")


if __name__ == "__main__":
    main()

