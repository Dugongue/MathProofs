import pathlib,sys,random,itertools,json,time,hashlib
HERE=pathlib.Path(__file__).parent;sys.path.insert(0,str(HERE));import full_controls as F
from modular_kernel import kernel_generators
from sympy import Matrix
rng=random.Random(20261106);t0=time.time();cases=0
for q in [4,8]:
 for n in range(1,5):
  for _ in range(12):
   m=rng.randrange(1,5);A=Matrix([[rng.randrange(q) for _ in range(n)] for _ in range(m)]);D,_,V=kernel_generators(A,q)
   gens=[tuple(int(V[i,j])*(q//int(D[j,j]))%q for i in range(n)) for j in range(n)]
   span={(0,)*n}
   for g in gens:span={tuple((a+k*b)%q for a,b in zip(v,g)) for v in span for k in range(q)}
   brute={v for v in itertools.product(range(q),repeat=n) if all(sum(int(A[i,j])*v[j] for j in range(n))%q==0 for i in range(m))};assert span==brute;cases+=1
orig=F.snf;orbitcases=0
for n in range(1,7):
 for _ in range(8):
  G=F.C.random_code(n,rng.randrange(n+1),rng);T=[j for j in range(n) if rng.randrange(2)];F.snf=orig;_,a,_,_=F.omega(G,T,n)
  q=1<<(2+len(T)*(len(T)+1).bit_length());F.snf=lambda M:kernel_generators(M,q);_,b,_,_=F.omega(G,T,n)
  assert F.rr([o['image'] for o in a])==F.rr([o['image'] for o in b]);orbitcases+=1
r={'status':'PASS','modular_kernel_vs_complete_bruteforce_cases':cases,'universal_grid_orbit_image_vs_integer_torus_Smith_cases':orbitcases,'elapsed_seconds':time.time()-t0,'scope':'Exact finite controls; universal grid coverage follows from the separate Cramer/dyadic proof.','sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()};(HERE/'MODULAR-CHECKS.json').write_text(json.dumps(r,indent=2)+'\n',encoding='utf-8');print(json.dumps(r,indent=2))
