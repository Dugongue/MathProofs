from itertools import permutations,product
from pathlib import Path
import hashlib,json

def check(q):
    E=(1,1,1)
    def mm(a,b):return tuple(x*y%q for x,y in zip(a,b))
    def setmul(a,b):return {mm(x,y) for x,y in product(a,b)}
    def subgen(x):
        ans={E};y=x
        while y not in ans: ans.add(y);y=mm(y,x)
        return ans
    # Three block isotypes; interleaving and mixed parities vary across modes.
    typesT=(0,1,0,2,1,0)
    typesS=(1,0,0,2,0,1)
    dims=((1,2,3),(2,1,2),(3,1,1))
    H=(subgen((2%q,2%q,1)),subgen((1,2%q,2%q)),{E})
    r=[(1+i%(q-1),1+(i+1)%(q-1),q-1) for i in range(6)]
    s=[(q-1,1+(i+2)%(q-1),1+i%(q-1)) for i in range(6)]
    cal=(q-1,2%q,1)
    def sign(perm):
        n=sum(a>b for i,a in enumerate(perm) for b in perm[i+1:])
        return 1 if n%2==0 else q-1
    def pos(order,mode):
        starts=[];j=0
        for c in order:starts.append(j);j+=dims[c][mode]
        return starts
    def perm_sign(pi):
        return tuple(sign([start[pi[i]]+k for i,c in enumerate(typesT)
                     for k in range(dims[c][j])])
                     for j in range(3) for start in [pos(typesS,j)])
    def local(pi):
        z={E}
        for i,j in enumerate(pi):
            z=setmul(z,{mm(mm(r[i],s[j]),h) for h in H[typesT[i]]})
        return z
    P=[p for p in permutations(range(6))
       if all(c==typesS[p[i]] for i,c in enumerate(typesT))]
    base=P[0];coset=local(base)
    assert all(local(p)==coset for p in P)
    actual=set()
    for p in P:actual.update(mm(cal,mm(perm_sign(p),x)) for x in local(p))
    eps=[tuple(1 if d%2==0 else q-1 for d in dims[c]) for c in (0,1)]
    S={E}
    for e in eps:S=setmul(S,{E,e})
    predicted={mm(cal,mm(perm_sign(base),mm(x,y))) for x,y in product(coset,S)}
    assert predicted==actual
    return {"q":q,"matchings":len(P),"full_joint_determinant_set_size":len(actual),
            "correlated_local_cosets":True,"all_coordinates_exact":"PASS"}

if __name__=="__main__":
    root=Path(__file__).parent
    report={"status":"PASS","controls":[check(q) for q in (3,5,7,11)],
        "scope":"Exact finite controls of the coset/sign identity on interleaved repeated block types; not a substitute for the proof."}
    (root/"DETERMINANT-AUDIT-CONTROLS.json").write_text(json.dumps(report,indent=2)+"\n",encoding="utf8")
    print(json.dumps(report))
