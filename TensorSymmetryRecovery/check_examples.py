"""Small independent checks. Only the Python standard library is needed."""
from itertools import permutations, product
from math import factorial

def field4(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        if a & 4:
            a ^= 7
        b >>= 1
    return out

def dual_number(a, b):
    return field4(a & 3, b & 3) ^ ((field4(a >> 2, b & 3) ^ field4(a & 3, b >> 2)) << 2)

def image(cols, x):
    y = 0
    for i, col in enumerate(cols):
        if (x >> i) & 1:
            y ^= col
    return y

def bases(r, cols=(), span=frozenset({0})):
    if len(cols) == r:
        yield cols
        return
    for v in range(1, 1 << r):
        if v not in span:
            yield from bases(r, cols+(v,), span | {u ^ v for u in span})

def algebra_example():
    basis = [1, 2, 4, 8]
    # In F4 the conjugates of the power basis are (1,2) and (1,3).
    primal = (set([1, 2, 3]) | set([0,4,8,12]))
    # Label covectors by their binary dot-product coefficient masks.
    # Duals of (1,2) and (1,3) are (1,2) and (3,2), respectively.
    dual = {0,1,2,3,4,8,12}
    checked = count = 0
    for cols in bases(4):
        checked += 1
        if all(image(cols, dual_number(a,b)) == dual_number(image(cols,a),image(cols,b))
               for a in basis for b in basis):
            count += 1
            assert {image(cols,x) for x in primal} == primal
            transpose = lambda d: sum(((d & c).bit_count() % 2) << i for i,c in enumerate(cols))
            assert {transpose(d) for d in dual} == dual
    assert (checked, count) == (20160, 6)
    return checked, count

def arity_examples():
    for b in range(1, 6):
        vectors = list(product(range(3), repeat=b+1))
        h = [x for x in vectors if sum(x)%3 == 0]
        k = [x for x in vectors if (sum(x)+x[-1])%3 == 0]
        assert set(h) != set(k)
        for i in range(b+1):
            proj = lambda g: {x[:i]+x[i+1:] for x in g}
            assert proj(h) == proj(k) and len(proj(h)) == 3**b
        group = list(product(range(3), repeat=b))
        def cost(x, raised):
            return int(any(x)) + int(raised and (x == (1,)*b or x == (2,)*b))
        for i in range(b):
            tables = []
            for raised in (False, True):
                table = {}
                for x in group:
                    key = x[:i]+x[i+1:]
                    table[key] = min(table.get(key, 3), cost(x, raised))
                tables.append(table)
            assert tables[0] == tables[1]
        assert cost((1,)*b, True) != cost((1,)*b, False)

def shear_example(r, n, m):
    mask = (1<<r)-1
    def shift(x): return (x<<1)&mask
    cols = list(product(range(1<<r), repeat=r))
    commuting = [c for c in cols if all(shift(c[i]) == image(c,shift(1<<i)) for i in range(r))]
    count = sum(all(all(shift(a^b)==0 for a,b in zip(xs[i],xs[(i+1)%n]))
                    for i in range(n)) for xs in product(commuting,repeat=n))
    assert count == 2**(r-1+n)
    return count*n*factorial(m)**n

if __name__ == "__main__":
    print("binary ring: invertible maps checked and ring automorphisms", algebra_example())
    arity_examples()
    print("both arity examples checked at b=1 through 5")
    print("cycle automorphism counts", [shear_example(*x) for x in [(1,3,2),(2,3,2),(2,4,1),(3,3,1)]])
