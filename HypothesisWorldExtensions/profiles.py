"""List exactly realizable finite-field module Hom profiles at selected moduli."""
import argparse
from math import lcm


def threshold(modulus):
    if modulus < 1:
        raise ValueError("Moduli must be positive integers")
    exponent = 0
    while modulus % 2 == 0:
        exponent += 1
        modulus //= 2
    if modulus == 1:
        return exponent, 1
    order = 1
    residue = 2 % modulus
    while residue != 1:
        residue = (2 * residue) % modulus
        order += 1
    return exponent, order


def profiles(moduli, graphs=False):
    bounds = [(0, m) for m in moduli] if graphs else list(map(threshold, moduli))
    representatives = {}
    for mask in range(1 << len(moduli)):
        a, b = 0, 1
        for j, (exponent, order) in enumerate(bounds):
            if mask >> j & 1:
                a, b = max(a, exponent), lcm(b, order)
        realized = sum(1 << j for j, (exponent, order) in enumerate(bounds)
                       if exponent <= a and b % order == 0)
        representatives[realized] = (a, b)
    return representatives


DEFAULT = [2, 3, 4, 5, 6, 7, 8, 9, 15, 21, 31, 63, 73]

def variable_field_profiles(moduli):
    result = {}
    for _, (_, divisor) in profiles(moduli, graphs=True).items():
        even = lcm(2, divisor)
        mask = sum(1 << j for j, m in enumerate(moduli) if even % m == 0)
        result[mask] = ("even-divisor", even)
    for _, (_, exponent) in profiles(moduli).items():
        mask = sum(1 << j for j, m in enumerate(moduli) if pow(2, exponent, m) == 1 % m)
        result[mask] = ("binary-exponent", exponent)
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--graphs", action="store_true", help="use graph Hom counts")
    group.add_argument("--all-fields", action="store_true", help="allow the finite field to vary")
    parser.add_argument("moduli", nargs="*", type=int, default=DEFAULT)
    args = parser.parse_args()
    choices = variable_field_profiles(args.moduli) if args.all_fields else profiles(args.moduli, args.graphs)
    for mask, (a, b) in sorted(choices.items()):
        print(a, b, [m for j, m in enumerate(args.moduli) if mask >> j & 1])
