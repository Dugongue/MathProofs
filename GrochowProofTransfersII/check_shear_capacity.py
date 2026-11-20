"""Exact finite controls for the two-coordinate STPP construction."""
from fractions import Fraction
from itertools import combinations, product
from math import gcd


def parameters(a, b, k, m):
    assert a > b > 0 and gcd(a, b) == 1
    distances = {a*i + b*j for i in range(k+1) for j in range(m+1) if i+j}
    d, r = divmod(a-b, k+m+1)
    assert r
    width = a*k + b*m
    if r <= m:
        return distances, width+b, b+k*d
    return distances, width+a, a-m*(d+1)


def brute(distances, n):
    neighbors = [sum(1 << j for j in range(n)
                     if j != i and ((j-i) % n in distances or (i-j) % n in distances))
                 for i in range(n)]
    best = -1
    winners = []
    def visit(active, chosen):
        nonlocal best, winners
        size = len(chosen)
        if size + active.bit_count() < best:
            return
        if not active:
            if size > best:
                best, winners = size, []
            if size == best:
                winners.append(chosen)
            return
        bit = active & -active
        i = bit.bit_length() - 1
        rest = active ^ bit
        visit(rest & ~neighbors[i], chosen + (i,))
        visit(rest, chosen)
    visit((1 << n) - 1, ())
    return best, set(winners)


def binary_trace(distances, n):
    width = max(distances)
    mask = (1 << width) - 1
    conflict = sum(1 << (f-1) for f in distances)
    edges = {}
    unseen = [0]
    while unseen:
        state = unseen.pop()
        if state in edges:
            continue
        shifted = state << 1 & mask
        edges[state] = [(shifted, 0)]
        if not state & conflict:
            edges[state].append((shifted | 1, 1))
        unseen.extend(other for other, _ in edges[state] if other not in edges)
    answer, number = -1, 0
    for root in edges:
        current = {root: (0, 1)}
        for _ in range(n):
            new = {}
            for old, (score, count) in current.items():
                for nxt, bit in edges[old]:
                    value = score + bit
                    prior, ways = new.get(nxt, (-1, 0))
                    if value > prior:
                        new[nxt] = value, count
                    elif value == prior:
                        new[nxt] = value, ways + count
            current = new
        if root not in current:
            continue
        score, count = current[root]
        if score > answer:
            answer, number = score, count
        elif score == answer:
            number += count
    return answer, number


def equality_words(distances, q, h, n):
    g = gcd(q, n)
    if h*g % q:
        return Fraction(0), set()
    k = h*g//q
    blocks = [(0,) + rest for rest in combinations(range(1, g), k-1)
              if all(b-a not in distances for a, b in combinations((0,) + rest, 2))]
    length, reach = n//g, (max(distances)+g-1)//g
    words = []
    def legal(word):
        return all(t*g + v - u not in distances
                   for j, left in enumerate(word) for t in range(1, reach+1)
                   for u in left for v in word[(j+t) % length])
    # This direct enumeration of the memory graph's words is for small controls.
    for word in product(blocks, repeat=length):
        if legal(word):
            words.append(word)
    total = Fraction(0)
    winners = set()
    for word in words:
        common = set(enumerate(word[0]))
        for block in word[1:]:
            common.intersection_update(enumerate(block))
        total += Fraction(g, len(common))
        unshifted = [j*g+b for j, block in enumerate(word) for b in block]
        for x in range(n):
            winners.add(tuple(sorted((x+y) % n for y in unshifted)))
    return total, winners


def check_case(case, n):
    distances, q, h = parameters(*case)
    max_size, max_sets = brute(distances, n)
    assert binary_trace(distances, n) == (max_size, len(max_sets)), (case, n)
    assert max_size*q <= n*h
    rate_cases = max_sets if max_size*q == n*h else set()
    weighted, reconstructed = equality_words(distances, q, h, n)
    assert reconstructed == rate_cases, (case, n, reconstructed, rate_cases)
    assert weighted == len(rate_cases), (case, n)
    return max_size, len(max_sets), len(rate_cases)


def verify_period_19_table():
    distances, q, h = parameters(5, 3, 2, 2)
    assert (q, h) == (19, 3)
    sites = [i for i in range(1, q) if i not in distances and q-i not in distances]
    blocks = [(0, a, b) for a, b in combinations(sites, 2) if b-a not in distances]
    assert blocks == [(0, 1, 2), (0, 1, 15), (0, 1, 18), (0, 2, 4),
                      (0, 2, 17), (0, 4, 18), (0, 15, 17), (0, 17, 18)]
    successors = [[j for j, B in enumerate(blocks)
                   if all(q + v - u not in distances for u in A for v in B)]
                  for A in blocks]
    assert successors == [list(range(8)), [6, 7], [2, 7], [3, 4, 5, 6, 7],
                          [4, 6, 7], [7], [6, 7], [7]]
    assert all(i <= j for i, row in enumerate(successors) for j in row)
    assert sum(i in row for i, row in enumerate(successors)) == 6
    print("Verified the 8-state table for all multiples of 19.")


def main():
    verify_period_19_table()
    groups = [(3, 1, 1, 2), (3, 2, 1, 1), (4, 1, 1, 2), (3, 1, 2, 1),
              (3, 2, 2, 1), (5, 3, 2, 1), (5, 3, 2, 2), (8, 1, 1, 2)]
    count = 0
    for case in groups:
        distances, _, _ = parameters(*case)
        for n in range(max(distances)+1, max(distances)+8):
            check_case(case, n)
            count += 1
    examples = [((4, 1, 1, 2), 15), ((3, 1, 2, 1), 15), ((5, 3, 2, 2), 19),
                ((5, 3, 2, 2), 38), ((5, 3, 2, 1), 27)]
    for case, n in examples:
        capacity, count_all, rate = check_case(case, n)
        print(f"{case}, N={n}: capacity={capacity}, maximizers={count_all}, rate-achievers={rate}")
    print(f"Verified {count + len(examples)} exact finite capacity and anchor-count controls.")


if __name__ == "__main__":
    main()
