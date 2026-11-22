from itertools import product
from math import gcd


def check_quadratic_norm(modulus, prime, b, c):
    """Norm of a + u*t for t^2 + b*t + c = 0."""
    assert all((t*t + b*t + c) % prime for t in range(prime))
    units = {a for a in range(modulus) if gcd(a, modulus) == 1}
    principal = {a for a in units if a % prime == 1}
    norm_image = set()
    principal_image = set()
    for a, u in product(range(modulus), repeat=2):
        norm = (a * (a - b*u) + c*u*u) % modulus
        if a % prime or u % prime:
            norm_image.add(norm)
        if a % prime == 1 and u % prime == 0:
            principal_image.add(norm)
    assert norm_image == units
    assert principal_image == principal
    return len(units), len(principal)


def check_square_zero_loop(modulus):
    """All automorphisms z -> a + b*z of (Z/modulus)[z]/(z^2)."""
    units = {b for b in range(modulus) if gcd(b, modulus) == 1}
    autos = {(a, b) for a, b in product(range(modulus), units)
             if a*a % modulus == 0 and 2*a*b % modulus == 0}
    assert {b for _, b in autos} == units
    assert (modulus // 2, 1) in autos
    return len(autos)


def main():
    for modulus in (4, 8, 16):
        size = check_quadratic_norm(modulus, 2, 1, 1)
        print(f"Z/{modulus}: quadratic unit and principal norm sizes {size}")
        print(f"Z/{modulus}: {check_square_zero_loop(modulus)} automorphisms of the loop algebra")
    for modulus in (9, 27):
        size = check_quadratic_norm(modulus, 3, 0, 1)
        print(f"Z/{modulus}: quadratic unit and principal norm sizes {size}")


if __name__ == '__main__':
    main()
