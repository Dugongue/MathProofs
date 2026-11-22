"""Check the unit-group indices and independent marker powers on small rings."""


def power(a, n, multiply):
    value = 1
    while n:
        if n & 1:
            value = multiply(value, a)
        a = multiply(a, a)
        n >>= 1
    return value


def probe(units, multiply, s, rho, order, index):
    power_group = {power(a, s, multiply) for a in units}
    assert rho not in power_group
    assert power(rho, order, multiply) == 1
    assert all(power(rho, j, multiply) != 1 for j in range(1, order))
    actual = {multiply(a, power(rho, j, multiply))
              for a in power_group for j in range(order)}
    assert len(units) // len(power_group) == index
    assert len(units) // len(actual) == index // order
    assert power(rho, 2 * s + 1, multiply) == rho
    assert all(power(t, 6 * s, multiply) in power_group for t in units)
    return len(units)


def truncated_binary(a, b, limit):
    value = 0
    while b:
        if b & 1:
            value ^= a
        a <<= 1
        b >>= 1
    return value & (limit - 1)


def main():
    cases = total_units = 0
    for e in range(2, 12):
        modulus = 2**e
        mul = lambda a, b: a * b % modulus
        units = list(range(1, modulus, 2))
        total_units += probe(units, mul, 2, modulus - 1, 2, 2 if e == 2 else 4)
        cases += 1
        e_width = 1 << (e - 1).bit_length()
        mul = lambda a, b: truncated_binary(a, b, modulus)
        rho = 1 | (1 << (e - 1))
        total_units += probe(units, mul, e_width, rho, 2, len(units))
        cases += 1
        if e == 3:
            total_units += probe(units, mul, 4, 3, 4, 4)
        else:
            r = (e + 1) // 2
            if r % 2 == 0:
                r += 1
            rho = 1 | (1 << r)
            total_units += probe(units, mul, 2, rho, 2, 2**(e // 2))
        cases += 1
    for prime in (3, 5, 7):
        s = (prime - 1) & -(prime - 1)
        for e in (1, 2, 3):
            modulus = prime**e
            units = [a for a in range(1, modulus) if a % prime]
            mul = lambda a, b: a * b % modulus
            total_units += probe(units, mul, s, modulus - 1, 2, s)
            cases += 1
    for prime in (3, 5, 7, 11, 13):
        c_p = ((prime - 1) & -(prime - 1)) * ((prime + 1) & -(prime + 1))
        for f in range(1, 65):
            value = prime**f - 1
            assert (value & -value) <= c_p * f
    print(f"{cases} calibrated ring cases and {total_units} unit checks")
    print("320 odd-residue-degree width bounds checked")


if __name__ == "__main__":
    main()
