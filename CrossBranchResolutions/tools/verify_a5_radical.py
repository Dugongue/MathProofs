from pathlib import Path
import json
from itertools import product
out=Path(__file__).resolve().parent
def fm(a,b):
    r=0
    while b:
        if b&1:r^=a
        b>>=1;a<<=1
        if a&4:a^=7
    return r
def mm(a,b):
    return tuple(fm(a[2*i],b[j])^fm(a[2*i+1],b[2+j]) for i in range(2) for j in range(2))
G=[a for a in product(range(4),repeat=4) if fm(a[0],a[3])^fm(a[1],a[2])==1]
pos={a:i for i,a in enumerate(G)}
mt=[[pos[mm(a,b)] for b in G] for a in G]
points=[(1,x) for x in range(4)]+[(0,1)]
def norm(v):
    first=next(x for x in v if x)
    inv=next(x for x in range(1,4) if fm(first,x)==1)
    return tuple(fm(inv,x) for x in v)
def image(a):
    perm=[points.index(norm((fm(a[0],v[0])^fm(a[1],v[1]),fm(a[2],v[0])^fm(a[3],v[1])))) for v in points]
    rep4=0
    for j in range(4):
        col=(1<<perm[j])^(1<<perm[4])
        for i in range(4):
            if col>>i&1:rep4|=1<<(4*j+i)
    natural=sum(x<<(2*i) for i,x in enumerate(a))
    return 1|(natural<<1)|(rep4<<9)
columns=[image(a) for a in G]
def targetmul(x,y):
    natx=tuple((x>>(1+2*i))&3 for i in range(4))
    naty=tuple((y>>(1+2*i))&3 for i in range(4))
    nat=mm(natx,naty)
    a=(x>>9)&65535;b=(y>>9)&65535;c=0
    for i in range(4):
        for j in range(4):
            entry=0
            for k in range(4):entry^=((a>>(4*k+i))&1)&((b>>(4*j+k))&1)
            c|=entry<<(4*j+i)
    return (x&y&1)|(sum(v<<(2*i+1) for i,v in enumerate(nat)))|(c<<9)
assert all(targetmul(columns[i],columns[j])==columns[mt[i][j]] for i in range(60) for j in range(60))
def basis(vs):
    piv={}
    for v in vs:
        while v:
            p=v.bit_length()-1
            if p in piv:v^=piv[p]
            else:piv[p]=v;break
    return list(piv.values())
piv={};ker=[]
for j,v in enumerate(columns):
    word=1<<j
    while v:
        p=v.bit_length()-1
        if p in piv:
            v^=piv[p][0];word^=piv[p][1]
        else:piv[p]=(v,word);break
    if not v:ker.append(word)
assert len(piv)==25 and len(ker)==35
def inds(x):
    while x:
        t=x&-x;yield t.bit_length()-1;x^=t
def mul(x,y):
    r=0;ys=list(inds(y))
    for i in inds(x):
        for j in ys:r^=1<<mt[i][j]
    return r
powers=[list(ker)];dims=[60,len(ker)]
while powers[-1]:
    nxt=basis(mul(x,y) for x in powers[-1] for y in ker)
    powers.append(nxt);dims.append(len(nxt))
    assert len(dims)<9
assert dims == [60,35,27,17,9,0]
# Explicit nonzero product of four radical elements.
witness=None
for x in ker:
    for y in ker:
        xy=mul(x,y)
        if not xy:continue
        for z in ker:
            xyz=mul(xy,z)
            if not xyz:continue
            for w in ker:
                ans=mul(xyz,w)
                if ans:witness=[hex(t) for t in [x,y,z,w,ans]];break
            if witness:break
        if witness:break
    if witness:break
identity=pos[(1,0,0,1)]
def order(i):
    j=i;n=1
    while j!=identity:j=mt[j][i];n+=1
    return n
e=sum(1<<i for i in range(60) if order(i)%2)
assert mul(e,e)==e
assert all(mul(e,1<<i)==mul(1<<i,e) for i in range(60))
block_basis=basis(mul(e,1<<i) for i in range(60))
other=((1<<identity)^e)
other_basis=basis(mul(other,1<<i) for i in range(60))
assert len(block_basis)==44 and len(other_basis)==16
assert all(mul(e,v)==v for v in ker)
# Upper triangular unipotent matrices form a Sylow subgroup P = V4.
P=[pos[(1,t,0,1)] for t in range(4)]
projection=e & sum(1<<i for i in P)
assert projection==1<<identity
# Center of the 44-dimensional corner: compute commutator map rank.
commcols=[]
for v in block_basis:
    column=0
    for i in range(60):column|=(mul(v,1<<i)^mul(1<<i,v))<<(60*i)
    commcols.append(column)
centerpiv={};center_basis=[]
for comm,v in zip(commcols,block_basis):
    while comm:
        lead=comm.bit_length()-1
        if lead in centerpiv:comm^=centerpiv[lead][0];v^=centerpiv[lead][1]
        else:centerpiv[lead]=(comm,v);break
    if not comm:center_basis.append(v)
def algebra_image(v):
    w=0
    for i in inds(v):w^=columns[i]
    return w
center_semisimple_rank=len(basis(algebra_image(v) for v in center_basis))
assert len(center_basis)==4 and center_semisimple_rank==1
# The central radical is nilpotent and the residue field is F2.
# Hence this corner is connected, including after extension of the field.
# Augmentation of e is 1, so this corner contains the trivial module.
assert e.bit_count()%2==1
result={'field' :'F2; F4 encoded by t^2+t+1','group':'SL2(F4), lexicographic tuples (a,b,c,d)','order':len(G),'semisimple_image_rank':len(piv),'radical_power_dimensions':dims,'nonzero_fourfold_product_hex':witness,'radical_basis_hex':[hex(x) for x in ker], 'all_representation_products_checked':3600,'central_idempotent_hex':hex(e),'principal_corner_dimension':len(block_basis),'complement_dimension':len(other_basis),'principal_corner_center_dimension':len(block_basis)-len(basis(commcols)),'projection_to_sylow':hex(projection),'center_semisimple_image_rank':center_semisimple_rank}
print(json.dumps(result,indent=2))
(out/'a5-radical-certificate.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\n')
