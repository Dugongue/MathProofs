"""Exhaustively check the sharp initial fixed-point prefix on small permutation degrees."""
from itertools import chain


def partitions(total, least=1):
    if not total:
        yield ()
    for first in range(least, total + 1):
        for rest in partitions(total - first, first):
            yield (first,) + rest


def profile(cycles, length):
    return tuple(sum(d for d in cycles if k % d == 0) for k in range(1, length + 1))


def recover(total, values):
    counts = {}
    for k, fixed in enumerate(values, 1):
        earlier = sum(d * a for d, a in counts.items() if k % d == 0)
        a, remainder = divmod(fixed - earlier, k)
        assert remainder == 0 and a >= 0
        counts[k] = a
    recovered = tuple(chain.from_iterable((d,) * a for d, a in counts.items()))
    tail = total - sum(recovered)
    assert tail == 0 or tail > len(values)
    return recovered + ((tail,) if tail else ())


if __name__ == "__main__":
    tested = 0
    for n in range(2, 31):
        m = n // 2
        for parts in partitions(n):
            assert recover(n, profile(parts, m)) == parts
            tested += 1
        assert profile((m,n-m),m-1) == profile((n,),m-1)
        assert profile((m,n-m),m) != profile((n,),m)
    print(f"Recovered all {tested} cycle types in degrees 2 through 30 and checked all 29 sharpness pairs.")
