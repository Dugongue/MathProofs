import itertools,json,time,pathlib
start=time.perf_counter()
fields=[(2,[1,1,1]),(2,[1,1,0,1]),(3,[1,0,1]),(2,[1,1,0,0,1]),(5,[2,0,1]),(3,[1,2,0,1]),(2,[1,0,1,0,0,1])]
records=[]
for p,mod in fields:
 m=len(mod)-1;q=p**m
 dig=[]
 for x in range(q):
  a=[]
  for _ in range(m):a.append(x%p);x//=p
  dig.append(a)
 def enc(a):return sum(z*p**i for i,z in enumerate(a))
 add=[[enc([(dig[a][i]+dig[b][i])%p for i in range(m)]) for b in range(q)] for a in range(q)]
 neg=[enc([(-z)%p for z in dig[a]]) for a in range(q)]
 mul=[]
 for a in range(q):
  row=[]
  for b in range(q):
   c=[0]*(2*m-1)
   for i in range(m):
    for j in range(m):c[i+j]=(c[i+j]+dig[a][i]*dig[b][j])%p
   for t in range(2*m-2,m-1,-1):
    z=c[t]
    for i in range(m+1):c[t-m+i]=(c[t-m+i]-z*mod[i])%p
   row.append(enc(c[:m]))
  mul.append(row)
 inv=[None]+[next(b for b in range(1,q) if mul[a][b]==1) for a in range(1,q)]
 def powf(a,n):
  b=1
  while n:
   if n&1:b=mul[b][a]
   a=mul[a][a];n>>=1
  return b
 alpha=p
 orbit=[powf(alpha,p**j) for j in range(m)]
 assert len(set(orbit))==m
 refs=[(1,0),(0,1),(1,1),(1,alpha)]
 survivors=[];checked=0
 for a in (0,1):
  triples=itertools.product(range(q),repeat=3) if a else ((1,c,d) for c in range(1,q) for d in range(q))
  for b,c,d in triples:
   if add[mul[a][d]][neg[mul[b][c]]]==0:continue
   for j in range(m):
    checked+=1;ok=True
    for x,y in refs:
     fx=powf(x,p**j);fy=powf(y,p**j)
     u=add[mul[a][fx]][mul[b][fy]];v=add[mul[c][fx]][mul[d][fy]]
     if mul[u][y]!=mul[v][x]:ok=False;break
    if ok:survivors.append({'B':[a,b,c,d],'frobenius_power':j})
 assert survivors==[{'B':[1,0,0,1],'frobenius_power':0}],survivors
 assert checked==(q**3-q)*m
 records.append({'p':p,'degree':m,'q':q,'irreducible_modulus_ascending':mod,'alpha':alpha,'frobenius_orbit':orbit,'projective_semilinear_maps_checked':checked,'labeled_reference_stabilizer':survivors})
 print(q,checked,survivors,flush=True)
result={'pass':True,'total_checks':sum(r['projective_semilinear_maps_checked'] for r in records),'seconds':time.perf_counter()-start,'scope':'Exhaustive PGL(2,q) times Frobenius reference stabilizers, not the universal theorem proof','fields':records}
out=pathlib.Path(__file__).resolve().with_name('REFERENCE-CHECKS.json');out.write_text(json.dumps(result,indent=2));print(json.dumps({k:result[k] for k in ('pass','total_checks','seconds')}))
