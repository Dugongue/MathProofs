"""Exact regression checks for a failed compiler; not a complexity proof."""
from itertools import product
import json

F = range(3)
def mul(a,b):
    return tuple(sum(a[2*i+k]*b[2*k+j] for k in range(2))%3
                 for i in range(2) for j in range(2))
def det(a): return (a[0]*a[3]-a[1]*a[2])%3
def inv(a):
    d=det(a)
    return tuple(d*v%3 for v in (a[3],-a[1],-a[2],a[0]))
G=[a for a in product(F,repeat=4) if det(a)]
U={(1,a,0,1) for a in F}
L={(1,0,a,1) for a in F}
count=0
for a,b in product(G,repeat=2):
    actual={mul(mul(a,u),inv(b)) for u in U} == U
    predicted=(a[2]==b[2]==0 and a[0]==b[0] and a[3]==b[3])
    assert actual==predicted
    count+=actual
assert count==36
assert (0,2,1,0) not in {mul(u,l) for u,l in product(U,L)}
points=set(product(range(2),repeat=2))
fibers=[]
for a,b,c in product(range(2),repeat=3):
    fiber={v for v in points if (a*v[0]+b*v[1]+c)%2==0}
    assert fiber != {(0,0)}
    fibers.append(len(fiber))
print(json.dumps({'status':'PASS','matrix_pairs':len(G)**2,
    'affine_slice_preservers':count,'affine_boolean_functions':len(fibers),
    'unrestricted_reduction_proved':False},indent=2))
