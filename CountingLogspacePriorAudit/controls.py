"""Exact carry-free Gaussian controls; Python stores integers and is not an FL implementation."""
import pathlib,json,math,time,hashlib
HERE=pathlib.Path(__file__).parent;t=time.time();coefs=0;diffs=0
# Independent recurrence G(M,K)=G(M-1,K-1)+q^K G(M-1,K).
polys={(0,0):[1]}
for M in range(1,33):
 for K in range(M+1):
  if K==0 or K==M:polys[M,K]=[1];continue
  a=polys[M-1,K-1];b=polys[M-1,K];z=[0]*max(len(a),K+len(b))
  for i,c in enumerate(a):z[i]+=c
  for i,c in enumerate(b):z[i+K]+=c
  polys[M,K]=z
for n in range(17):
 for k in range(17):
  W=n+k+2;B=1<<W;num=math.prod((1<<(W*(n+i)))-1 for i in range(1,k+1));den=math.prod((1<<(W*i))-1 for i in range(1,k+1));Q,rem=divmod(num,den);assert rem==0
  expected=polys[n+k,k]
  for r,c in enumerate(expected):
   got=(Q>>(W*r))&(B-1);assert got==c;coefs+=1
   if 2*r<=n*k:
    prev=((Q>>(W*(r-1)))&(B-1)) if r else 0;assert got-prev>=0;assert got-prev==c-(expected[r-1] if r else 0);diffs+=1
r={'status':'PASS','rectangle_parameters':289,'exact_no_carry_coefficients_checked':coefs,'Hermite_adjacent_differences_checked':diffs,'max_n':16,'max_k':16,'elapsed_seconds':time.time()-t,'scope':'Own independent exact arithmetic controls only; no prior repository code copied; no logspace benchmark or complexity proof claim.','source_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()};(HERE/'CHECKS.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
