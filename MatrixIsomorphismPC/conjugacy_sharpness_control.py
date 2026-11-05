from fractions import Fraction as F
from pathlib import Path
import json,time
P=Path(__file__).parent;start=time.time()
# X entries are the index of a..h, or None.
X=[[0,2,1,3],[None,0,None,1],[None,4,None,5],[None,6,None,7]]
cols=[(z,i,j) for z in range(8) for i in range(4) for j in range(4)];idx={v:k for k,v in enumerate(cols)}
rows=[]
for side in ['XY','YX']:
 for i in range(4):
  for j in range(4):
   row=[F(0)]*129
   for k in range(4):
    z=X[i][k] if side=='XY' else X[k][j]
    if z is not None:row[idx[z,k,j] if side=='XY' else idx[z,i,k]]+=1
   row[-1]=F(i==j);rows.append(row)
mat=[r[:] for r in rows];piv=[];rr=0
for c in range(128):
 k=next((k for k in range(rr,len(mat)) if mat[k][c]),None)
 if k is None:continue
 mat[rr],mat[k]=mat[k],mat[rr];a=mat[rr][c];mat[rr]=[x/a for x in mat[rr]]
 for k in range(len(mat)):
  if k!=rr:
   a=mat[k][c];mat[k]=[x-a*y for x,y in zip(mat[k],mat[rr])]
 piv.append(c);rr+=1
 if rr==len(mat):break
assert all(any(r[:-1]) or not r[-1] for r in mat)
sol=[F(0)]*128
for r,c in zip(mat,piv):sol[c]=r[-1]
assert all(sum(a*b for a,b in zip(r[:-1],sol))==r[-1] for r in rows)
nonzero=[{'monomial':chr(97+z)+f'*y{i+1}{j+1}','value':str(sol[k])} for k,(z,i,j) in enumerate(cols) if sol[k]]
r={'status':'PASS','input':'A=J2+J2, B=J2+0+0, n=4; E=XA-BX, XY=YX=I','number_of_cross_moments':128,'inverse_equations':32,'linear_system_rank':rr,'nonzero_moments':nonzero,'unspecified_cross_moments':'zero','linear_and_same_side_quadratic_moments':'zero','constant_moment':'one','elapsed_s':time.time()-start,'scope':'Exact rational linear functional; proof additionally shows no lower-degree PC lines can arise from the substituted quadratic-plus-constant inverse system.'}
(P/'CONJUGACY-SHARPNESS-CONTROL.json').write_text(json.dumps(r,indent=2),encoding='utf8');print(json.dumps(r,indent=2))
