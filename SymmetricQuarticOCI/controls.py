"""Exact arithmetic checks for the one-block symmetric quartic construction."""
import itertools as it, json, math, random, time
from collections import defaultdict
from fractions import Fraction as F
from pathlib import Path
def identity(m):return [[int(i==j) for j in range(m)] for i in range(m)]
def mul(A,B):
 m=len(A);return [[sum(A[i][k]*B[k][j] for k in range(m)) for j in range(m)] for i in range(m)]
COLORS=((0,1,2,3),(0,2,1,3))
def swap_sym(out,key,v):
 i,j,k,l=key
 for a in [(i,j),(j,i)]:
  for b in [(k,l),(l,k)]:out[a+b]+=v

def encode(xx,n):
 y=defaultdict(F)
 for t,colors in zip(xx,COLORS):
  for v,c in t.items():swap_sym(y,tuple(a*n+b for a,b in zip(colors,v)),c)
 for a in range(4):
  for i,j in it.product(range(n),repeat=2):swap_sym(y,(a*n+i,a*n+j,a*n+i,a*n+j),F(a+1,2*(n+1)))
 for a,b in it.permutations(range(4),2):
  c,d=[e for e in range(4) if e not in (a,b)]
  for i,j in it.product(range(n),repeat=2):
   swap_sym(y,(b*n+i,c*n+j,a*n+i,c*n+j),F(1,n))
   swap_sym(y,(b*n+i,d*n+j,a*n+i,d*n+j),F(-1,n))
 return {k:v for k,v in y.items() if v}

def partial(y,m):
 a=[[F(0)]*m for _ in range(m)]
 for (i,j,k,l),v in y.items():
  if j==l:a[i][k]+=v
 return a

def units(y,n):
 m=4*n;D=partial(y,m);I=identity(m);p=[]
 for a in range(1,5):
  pa=I
  for e in range(1,5):
   if e!=a:pa=mul(pa,[[(D[i][j]-e*I[i][j])/(a-e) for j in range(m)] for i in range(m)])
  p.append(pa)
 psq=[mul(a,a) for a in p]
 q={}
 for a,b in it.product(range(4),repeat=2):
  if a==b:q[a,b]=p[a];continue
  c=min(e for e in range(4) if e not in (a,b));z=[[F(0)]*m for _ in range(m)]
  cols=[[(r,p[b][r][i]) for r in range(m) if p[b][r][i]] for i in range(m)]
  rows=[[(s,p[a][k][s]) for s in range(m) if p[a][k][s]] for k in range(m)]
  for (i,j,k,l),v in y.items():
   w=v*psq[c][l][j]
   if w:
    for r,bi in cols[i]:
     for s,ak in rows[k]:z[r][s]+=w*bi*ak
  q[a,b]=z
 return D,q

def action(y,g,h):
 m=len(g);z=defaultdict(F)
 cols=[[(r,g[r][i]) for r in range(m) if g[r][i]] for i in range(m)]
 rows=[[(s,h[i][s]) for s in range(m) if h[i][s]] for i in range(m)]
 for (i,j,k,l),v in y.items():
  for choices in it.product(cols[i],cols[j],rows[k],rows[l]):
   z[tuple(r for r,_ in choices)]+=v*math.prod(a for _,a in choices)
 return {k:v for k,v in z.items() if v}

def source(xx,n,types,pi):
 L=len(pi);tot=0
 for v in it.product(range(n),repeat=L):
  d=[0]*L
  for j,k in enumerate(pi):d[k]=v[j]
  tot+=math.prod(xx[t].get(v[2*i:2*i+2]+tuple(d[2*i:2*i+2]),0) for i,t in enumerate(types))
 return tot

def lifted(y,Q,types,pi):
 L=len(pi);m=len(Q[0,0]);a=[c for t in types for c in COLORS[t][:2]];b=[c for t in types for c in COLORS[t][2:]]
 edge=[]
 for j,k in enumerate(pi):
  e=Q[a[j],b[k]]
  edge.append([(s,r,e[r][s]) for r in range(m) for s in range(m) if e[r][s]])
 tot=0
 for z in it.product(*edge):
  v=tuple(e[0] for e in z);d=[0]*L
  for j,k in enumerate(pi):d[k]=z[j][1]
  tot+=math.prod(e[2] for e in z)*math.prod(y.get(v[2*i:2*i+2]+tuple(d[2*i:2*i+2]),0) for i in range(len(types)))
 return tot

def run():
 rng=random.Random(251142);start=time.time();base=0;cross=0;same=0;moved=0;routers=0;branches={}
 for n in [1,2,3]:
  m=4*n;xx=[{v:rng.randint(-3,3) for v in it.product(range(n),repeat=4)} for _ in range(2)]
  y=encode(xx,n);D,Q=units(y,n)
  assert D==[[(i//n+1)*int(i==j) for j in range(m)] for i in range(m)]
  for (a,b),q in Q.items():
   assert q==[[int(r//n==b and s//n==a and r%n==s%n) for s in range(m)] for r in range(m)];routers+=1
  for types in [(0,),(1,),(0,0),(0,1),(1,0),(1,1),(0,1,0),(1,0,1)]:
   L=2*len(types)
   perms=list(it.permutations(range(L))) if L<=4 else [rng.sample(range(L),L) for _ in range(9)]
   for pi in perms:
    assert source(xx,n,types,pi)==lifted(y,Q,types,pi);base+=1
    aa=[c for t in types for c in COLORS[t][:2]];bb=[c for t in types for c in COLORS[t][2:]]
    if len(set(types))>1:cross+=1
    if any(aa[j]==bb[k] for j,k in enumerate(pi)):same+=1
  for step in range(2):
   g=identity(m);h=identity(m);i=rng.randrange(n);j=n+rng.randrange(n);v=rng.choice([1,2,-1]);g[i][j]=v;h[i][j]=-v
   yy=action(y,g,h);DD,QQ=units(yy,n)
   assert DD==mul(mul(g,D),h)
   for ab,q in Q.items():assert QQ[ab]==mul(mul(g,q),h);routers+=1
   for types in [(0,),(1,),(0,1),(1,0,1)]:
    L=2*len(types);pi=rng.sample(range(L),L)
    assert source(xx,n,types,pi)==lifted(yy,QQ,types,pi);moved+=1
 # Known degeneration: both vector factors carry weight 1, both dual factors weight 0.
 n=2;zero=encode([{},{}],n);y=encode([{(0,0,1,1):1},{}],n);dz={k:y.get(k,0)-zero.get(k,0) for k in y.keys()|zero.keys()}
 for t in [F(1,2),F(2),F(-1)]:
  g=identity(8);h=identity(8)
  for j in range(0,8,2):g[j][j]=t;h[j][j]=1/t
  z=action(y,g,h);assert all(z.get(k,0)==zero.get(k,0)+t*t*dz.get(k,0) for k in z.keys()|dz.keys())
 result={'status':'PASS','dimensions_n':[1,2,3],'router_identity_checks':routers,'lifted_source_contractions':base,'mixed_block_contractions':cross,'contractions_with_same_color_cross_edge':same,'arbitrary_non_color_preserving_conjugated_contractions':moved,'known_nonclosed_orbit_path_exact_values':3,'seconds':time.time()-start,'arithmetic':'exact fractions, full sparse symmetric tensor and actual polynomial router extraction','Lean_checks':0}
 (Path(__file__).parent/'QUARTIC-CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2))
if __name__=='__main__':run()
