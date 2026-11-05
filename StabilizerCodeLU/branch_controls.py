"""Replay frozen small controls with explicit branch/image accounting."""
import sys,pathlib,json,time,hashlib
HERE=pathlib.Path(__file__).parent;sys.path.insert(0,str(HERE));import full_controls as F
stats={'T_empty_factors':0,'T_nonempty_W_empty_factors':0,'mixed_T_W_factors':0,'omega_basis_vectors':0,'omega_actual_label_space_changes':0,'omega_pure_gauge_representative_changes':0}
origomega=F.omega;origmatch=F.matching

def om(gs,T,n):
    z=origomega(gs,T,n);G,basis,D,K=z;S=[F.label(g,n) for g in G]
    for b in basis:
        stats['omega_basis_vectors']+=1
        if all(F.member(v,S) for v in b['delta']):stats['omega_pure_gauge_representative_changes']+=1
        else:stats['omega_actual_label_space_changes']+=1
    return z

def matching(gs,hs,n,T,W,orbit=None):
    stats['T_empty_factors' if not T else ('mixed_T_W_factors' if W else 'T_nonempty_W_empty_factors')]+=1
    return origmatch(gs,hs,n,T,W,orbit)
F.omega=om;F.matching=matching
start=time.time();F.run()
# Coupled [[6,3]] code with T={0,1}, W={2,3,4,5} under our fixed greedy order.
G=[(0,60,0),(0,0,60),(0,0,15)];H=list(G)
for j,key in enumerate(list(F.CLIFF)):H=F.apply_local(H,j,F.CLIFF[key])
ax=F.axes(G,H,6);assert ax is not None;gg,hh,T,W=ax;assert T==[0,1] and W==[2,3,4,5],(T,W)
assert F.full(G,H,6) and F.full(G,H,6,True)
d={'status':'PASS','branch_counts_across_actual_small_algorithm_factors':stats,'additional_coupled_mixed_fixture':{'n':6,'k':3,'source_generators_h_x_z':G,'T':T,'W':W,'full_algorithm_and_exhaustive_oracle_agree':True},'elapsed_seconds':time.time()-start,'scope':'Counts include 72 standalone omega systems plus omega calls inside 143-case replay and one additional mixed fixture. Gauge means corrections only rewrite stabilizer representatives; label-space change is checked against the source binary span.','sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest()}
(HERE/'BRANCH-CHECKS.json').write_text(json.dumps(d,indent=2)+'\n',encoding='utf-8');print(json.dumps(d,indent=2))
