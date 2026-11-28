#!/usr/bin/env python3
"""Exact finite checks for the explicitly defined Ext representative.

This verifies arithmetic samples, not the topological theorem and not the
infinite nonsplitting assertion. Those assertions have proofs in the manuscript.
Python 3.8 or later is sufficient; no third-party packages are used.
"""
from fractions import Fraction
from math import factorial
from pathlib import Path
import json


def split_factorial(j):
    f = factorial(j)
    q = f & -f
    return f, q, f // q


def z(j):
    f, q, odd = split_factorial(j)
    return 0 if q == 1 else odd * ((-pow(odd, -1, q)) % q)


def a(j):
    numerator = z(j) - z(j + 1)
    f = factorial(j)
    assert numerator % f == 0
    return numerator // f


def local_primitive(j, p):
    return Fraction(z(j) + (1 if p == 2 else 0), factorial(j))


def main():
    bound = 100
    primes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31,
              37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79,
              83, 89, 97, 101]
    recurrence_checks = 0
    for j in range(1, bound + 2):
        f, q, odd = split_factorial(j)
        value = z(j)
        assert 0 <= value < f
        assert (value + 1) % q == 0
        assert value % odd == 0
    for j in range(1, bound + 1):
        assert (z(j + 1) - z(j)) % factorial(j) == 0
        for p in primes:
            x = local_primitive(j, p)
            y = local_primitive(j + 1, p)
            assert x.denominator % p != 0
            assert y.denominator % p != 0
            assert x - (j + 1) * y == a(j)
            recurrence_checks += 1
        rational_x = Fraction(z(j), factorial(j))
        rational_y = Fraction(z(j + 1), factorial(j + 1))
        assert rational_x - (j + 1) * rational_y == a(j)
    result = {
        "status": "COMPUTATIONAL",
        "confidence": 1.0,
        "arithmetic": "exact integers and rational numbers",
        "checked_indices": [1, bound],
        "primes": primes,
        "local_recurrence_checks": recurrence_checks,
        "rational_recurrence_checks": bound,
        "passed": True,
        "scope": "Finite arithmetic checks only; the manuscript proves the infinite statement and the topology.",
        "initial_values": [
            {"j": j, "factorial": factorial(j), "z_j": z(j), "a_j": a(j),
             "x_j_at_2": str(local_primitive(j, 2)),
             "x_j_at_odd_primes": str(local_primitive(j, 3))}
            for j in range(1, 13)
        ],
    }
    output = Path(__file__).with_name("arithmetic_results.json")
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
