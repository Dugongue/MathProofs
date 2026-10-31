from pathlib import Path
from itertools import product
from collections import Counter
import json,hashlib
# Independent whole ambient GL4(F2) check of the F4 -> F2 descent frame.
root=Path(__file__).parent
def mul(a,b):
    v=0
    for i in range(2):
        if b>>i&1:v^=a<<i
    if v&4:v^=7
    return v
cols=[];roles={}
for a in (1,2,3):
    vectors=(a,a<<2,a|(a<<2),mul(2,a)|(a<<2))
    for role,v in enumerate(vectors):
        assert v not in roles
        roles[v]=role
        cols.extend([v]*(role+1))
assert len(cols)==30
counts=Counter(cols);accepted=[];gl=0
for bs in product(range(16),repeat=4):
    table=[0]
    for b in bs:table += [x^b for x in table]
    if len(set(table))<16:continue
    gl+=1
    if Counter({table[v]:m for v,m in counts.items()})==counts:
        accepted.append(bs)
assert gl==20160 and len(accepted)==3
# All 16 codewords, rather than sampled distance controls.
weights=[]
for a in range(1,16):
    weights.append(sum((a&v).bit_count()%2 for v in cols))
minimum=min(weights)
R=5;N=R*len(cols);repeated=[v for v in cols for _ in range(R)]
assert minimum*R>4
# Gaussian systematic form of actual repeated-code generator, with exact integer basis.
rows=[[(v>>i)&1 for v in repeated] for i in range(4)]
piv=[];rank=0
for j in range(N):
    z=next((i for i in range(rank,4) if rows[i][j]),None)
    if z is None:continue
    rows[rank],rows[z]=rows[z],rows[rank]
    for i in range(4):
        if i!=rank and rows[i][j]:rows[i]=[a^b for a,b in zip(rows[i],rows[rank])]
    piv.append(j);rank+=1
    if rank==4:break
assert rank==4
order=piv+[j for j in range(N) if j not in piv]
sys=[[row[j] for j in order] for row in rows]
assert [r[:4] for r in sys]==[[int(i==j) for j in range(4)] for i in range(4)]
basis=[]
for i in range(N):
    if i<4:row=sys[i][:]
    else:row=[2*int(i==j) for j in range(N)]
    restored=[0]*N
    for j,original in enumerate(order):restored[original]=row[j]
    basis.append(restored)
codewords={tuple((a&v).bit_count()%2 for v in repeated) for a in range(16)}
assert all(tuple(x%2 for x in row) in codewords for row in basis)
(root/'EXAMPLE-BASIS.json').write_text(json.dumps({'field':'F4=F2[t]/(t^2+t+1)','input_generator':[[1]],'basis_rows':basis,'rank':N,'code_dimension':4,'systematic_column_order':order,'minimum_code_weight':minimum*R,'determinant':'2^146'}))
rec={'status':'PASS','whole_ambient_GL4_F2_size':gl,'accepted_descent_row_maps':accepted,'expected_field_scalar_count':3,'all_15_nonzero_codeword_weights':dict(Counter(weights)),'unrepeated_length':30,'prime_code_rank':4,'repeat_factor':R,'lattice_rank':N,'repeated_minimum_distance':minimum*R,'shortest_squared_lattice_norm':4,'shortest_frame':'exactly +/-2 e_i by checked minimum distance and the separate universal proof','basis_modp_membership_all_rows':True,'basis_determinant':'2^146','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'meaning':'complete finite descent-group and code/basis checks; not Lean and not a novelty certificate'}
(root/'CHECKS.json').write_text(json.dumps(rec,indent=2))
print(json.dumps(rec))
