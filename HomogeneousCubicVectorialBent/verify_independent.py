from pathlib import Path
from collections import Counter
import json,hashlib
base=Path(__file__).resolve().parent;d=json.loads((base/'WITNESS.json').read_text())
# Independent polynomial long-division field arithmetic.
mod=d['field_modulus']
def mul(x,y):
    v=0
    for i in range(y.bit_length()):
        if y&(1<<i): v^=x<<i
    while v.bit_length()>=mod.bit_length(): v^=mod<<(v.bit_length()-mod.bit_length())
    return v
def trace(x):
    v=0
    for i in range(5):
        v^=x;x=mul(x,x)
    assert v in (0,1)
    return v
# Every nonzero field element has an inverse; irreducibility not merely presumed.
assert all(any(mul(x,y)==1 for y in range(1,32)) for x in range(1,32))
B=d['basis'];points=[];values=[];linear=[]
cert=json.loads((base/'ALGEBRAIC-CERTIFICATE.json').read_text())
assert B==cert['basis_columns']
def apply_basis(columns,v):
    out=0
    for i,c in enumerate(columns):
        if v>>i&1:out^=c
    return out
assert all(apply_basis(cert['inverse_basis_columns'],B[i])==1<<i for i in range(10))
def raw(v):
    x=v%32; y=v//32; out=0
    for i,a in enumerate(d['multipliers']):
        t=trace(mul(mul(a,x),y))
        for mask in d['g_masks'][i]:
            t^=int((y|mask)==y)
        out+=t<<i
    return out
linear=[raw(v) for v in B]
for z in range(1024):
    v=l=0
    for i in range(10):
        if z&(1<<i): v^=B[i];l^=linear[i]
    points.append(v); values.append(raw(v)^l)
assert len(set(points))==1024
assert values==json.loads((base/'TRUTH-TABLE.json').read_text())
components=[]
for selector in (1,2,3):
    f=[(selector&v).bit_count()%2 for v in values]
    coeff=[]
    # Direct subset sums, deliberately not the worker's butterfly Mobius algorithm.
    for s in range(1024):
        a=0;t=s
        while True:
            a^=f[t]
            if not t:break
            t=(t-1)&s
        if a:coeff.append(s)
    assert coeff and all(s.bit_count()==3 for s in coeff)
    published=json.loads((base/'ANF.json').read_text())['components'][selector-1]
    assert published['selector']==selector and coeff==published['monomials']
    # Direct character sums, deliberately not the worker's FWHT.
    hist=Counter(sum(1-2*(f[x]^((a&x).bit_count()%2)) for x in range(1024)) for a in range(1024))
    assert set(hist)=={-32,32}
    components.append({'selector':selector,'degree':3,'number_of_monomials':len(coeff),'Walsh_histogram':dict(hist),'ANF_masks':coeff})
rec={'status':'PASS','field_checked_by_all_nonzero_inverses':True,'basis_rank':10,'all_nonzero_components_checked':True,'independent_methods':'polynomial long division, direct subset sums, direct Walsh character sums','components':components,'truth_table_sha256':hashlib.sha256(bytes(values)).hexdigest(),'witness_sha256':hashlib.sha256((base/'WITNESS.json').read_bytes()).hexdigest(),'scope':'exact finite arithmetic; not Lean verification and not novelty evidence'}
(base/'INDEPENDENT-CHECKS.json').write_text(json.dumps(rec,indent=2))
print(json.dumps({k:v for k,v in rec.items() if k!='components'}))
print([(c['selector'],c['number_of_monomials'],c['Walsh_histogram']) for c in components])
