from itertools import product

def rot(x):
    return (x >> 1) | ((x & 1) << 2)
count=0
for mask in range(256):
    s={x for x in range(8) if mask&(1<<x)}
    if any(rot(x) not in s for x in s):
        continue
    if any(x^y^z not in s for x,y,z in product(s,repeat=3)):
        continue
    assert any(x&1==0 for x in s)==any(x&3==0 for x in s)
    assert (0 in s)==any(x.bit_count()%2==0 for x in s)
    count+=1
assert count==7
print("All seven rotation-invariant affine sign profiles, including the empty profile, passed.")
