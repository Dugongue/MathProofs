"""Exact rational checks for both tangency-flattening factor choices."""

from fractions import Fraction
from itertools import combinations, product
from math import comb


def multiply(a, b):
    if a == 0:
        return b
    if b == 0:
        return a
    return None


def dual_multiply(a, beta):
    if a == 0:
        return beta
    if a == beta:
        return 0
    return None


def add(column, index, value):
    result = column.get(index, 0) + value
    if result:
        column[index] = result
    else:
        column.pop(index, None)


def reduce_column(pivots, column):
    while column:
        row = min(column)
        if row not in pivots:
            coefficient = column[row]
            pivots[row] = {
                index: Fraction(value, coefficient)
                for index, value in column.items()
            }
            return
        factor = column[row]
        for index, value in pivots[row].items():
            add(column, index, -factor * value)


def rank(dimension, wedge_output):
    basis = range(dimension + 1)
    pivots = {}
    for i, j, k in combinations(basis, 3):
        for a, b in product(basis, repeat=2):
            column = {}
            for shift, first, second in ((i, j, k), (j, k, i), (k, i, j)):
                for left, right, sign in ((first, second, 1), (second, first, -1)):
                    if wedge_output:
                        ll, rr = dual_multiply(a, left), dual_multiply(b, right)
                    else:
                        ll, rr = multiply(a, left), dual_multiply(right, b)
                    if ll is not None and rr is not None:
                        add(column, (shift, ll, rr), sign)
            reduce_column(pivots, column)
    return len(pivots)


def main():
    for d in range(3, 10):
        n = d + 1
        tangent = d * comb(d + 1, 2)
        predicted = n * (n - 1) * (n - 2) + d * n - tangent
        output_rank = rank(d, wedge_output=True)
        input_rank = rank(d, wedge_output=False)
        assert output_rank == comb(d + 3, 3)
        assert input_rank == predicted
        assert output_rank != input_rank
        print(f"d={d} tangent={tangent} output rank={output_rank} input rank={input_rank}")


if __name__ == "__main__":
    main()
