from pathlib import Path
from itertools import product
import json,hashlib
# Full GL3(F4) semilinear row action on a whole wrapped code: detects cross-block mixing.
def mul(a,b):
    z=0
    for i in range(2):
        if b>>i&1:z^=a<<i
    if z&4:z^=7
    return z
M=[[mul(a,b) for b in range(4)] for a in range(4)]
inv={a:next(b for b in range(1,4) if M[a][b]==1) for a in range(1,4)}
def project(v):
    a=next((x for x in v if x),None)
    return tuple(M[inv[a]][x] for x in v) if a else tuple(v)
def act(A,v,j):
    v=tuple(M[x][x] for x in v) if j else v
    return tuple(M[A[3*i]][v[0]]^M[A[3*i+1]][v[1]]^M[A[3*i+2]][v[2]] for i in range(3))
def det(A):
    a,b,c,d,e,f,g,h,i=A
    return M[a][M[e][i]^M[f][h]] ^ M[b][M[d][i]^M[f][g]] ^ M[c][M[d][h]^M[e][g]]
# Original rank1 one-column code. Four reference multiplicities 2,3,4,5 are unique.
reps=[(1,0,0),(0,1,0),(0,0,1),(0,1,1),(0,1,2)]
expected=list(map(project,reps));counts=[0,0];gl=0
for A in product(range(4),repeat=9):
    if not det(A):continue
    gl+=1
    for j in (0,1):
        if all(project(act(A,v,j))==p for v,p in zip(reps,expected)):
            counts[j]+=1
assert gl==181440 and counts==[9,0]
# A concrete original GCE YES / LCE NO pair: distinct multiplicities pin cross ratio.
source=[(1,0),(0,1),(1,1),(1,2)];target=[(1,0),(0,1),(1,1),(1,3)]
counts2=[0,0]
for A in product(range(4),repeat=4):
    a,b,c,d=A
    if M[a][d]^M[b][c]==0:continue
    for j in (0,1):
        good=True
        for v,w in zip(source,target):
            x,y=v
            if j:x,y=M[x][x],M[y][y]
            out=(M[a][x]^M[b][y],M[c][x]^M[d][y])
            if project(out)!=project(w):good=False;break
        if good:counts2[j]+=1
assert counts2==[0,3]
rec={'status':'PASS','method':'exhaustive full GL3(F4) and Frobenius action, plus explicit linear-NO semilinear-YES control','GL3_F4_size':gl,'wrapped_automorphism_counts_by_Frobenius_power':counts,'unwrapped_control_transporter_counts_by_Frobenius_power':counts2,'wrapping':'one data column and four labelled reference projective classes with multiplicities2,3,4,5','meaning':'no nonidentity Frobenius or cross-block row transporter survives in this complete finite case; general theorem has separate proof','checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
Path(__file__).with_name('WHOLE-CHECKS.json').write_text(json.dumps(rec,indent=2))
print(json.dumps(rec))
