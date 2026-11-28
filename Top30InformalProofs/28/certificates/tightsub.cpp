// Restricted (sound for UNSAT) encoding of the CYCLE_3[L]-loop condition in Pol(LO2, LO_q).
// Unknown f on a finite family F of subsets of the n=3L coordinates (tuples of CYCLE_3[L]).
// Identifications: f(S_1(W)) = f(S_2(W)) = f(S_3(W)) for W subset Z_L, S_k(W) = {h : h_k in W}.
// Constraints: (f(X),f(Y),f(Z)) in LO_q for every ordered partition X,Y,Z of [n] with X,Y,Z in F.
// F = level-0 sets S_k(W) plus (level 1) complements of unions of two disjoint level-0 sets,
// plus (optional level 2) unions X u Y of disjoint level-0 sets.
// UNSAT of this subsystem => the full loop condition fails => PCSP(LO2,LO_q) NP-hard (BGKR Thm 2.1).
// usage: tightsub L q level out.cnf
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <array>
#include <map>
#include <set>
#include <algorithm>
#include <unordered_map>
using namespace std;
typedef unsigned long long u64;
int L,q,n;
bool lo(int a,int b,int c){int m=max(a,max(b,c)); return (a==m)+(b==m)+(c==m)==1;}
int main(int argc,char**argv){
  L=atoi(argv[1]); q=atoi(argv[2]); int level=atoi(argv[3]); n=3*L;
  vector<array<int,3>> H; for(int t=0;t<L;t++){int a=t,b=(t+1)%L,c=(t+2)%L; H.push_back({a,b,c}); H.push_back({b,c,a}); H.push_back({c,a,b});}
  u64 ALL=(n==64)?~0ULL:((1ULL<<n)-1);
  unordered_map<u64,int> id; vector<u64> sets;
  auto get=[&](u64 s){ auto it=id.find(s); if(it!=id.end()) return it->second; int k=sets.size(); id[s]=k; sets.push_back(s); return k; };
  vector<int> par;
  vector<u64> lvl0;
  vector<array<int,2>> idents;
  for(int W=0;W<(1<<L);W++){ int ix[3];
    for(int k=0;k<3;k++){ u64 s=0; for(int h=0;h<n;h++) if(W>>H[h][k]&1) s|=1ULL<<h; ix[k]=get(s); lvl0.push_back(s); }
    idents.push_back({ix[0],ix[1]}); idents.push_back({ix[0],ix[2]}); }
  int smalls=argc>5?atoi(argv[5]):0; for(u64 s=1;s<=ALL;s++){ if(__builtin_popcountll(s)<=smalls){ lvl0.push_back(s); get(s);} if(s>(1ULL<<n)) break; }
  sort(lvl0.begin(),lvl0.end()); lvl0.erase(unique(lvl0.begin(),lvl0.end()),lvl0.end());
  printf("level0 sets: %zu\n",lvl0.size());
  vector<array<int,3>> cons;
  // level 1: X,Y disjoint level0, Z = complement
  for(size_t i=0;i<lvl0.size();i++) for(size_t j=0;j<lvl0.size();j++){ u64 X=lvl0[i],Y=lvl0[j]; if(X&Y) continue; u64 Z=ALL&~(X|Y);
      int a=get(X),b=get(Y),c=get(Z); cons.push_back({a,b,c}); if(level>=2){ get(X|Y); } }
  if(level>=2){ // partitions with one part = union of two disjoint level0 sets, others level0
    vector<u64> pool(sets.begin(),sets.end());
    for(u64 X:pool) for(u64 Y:lvl0){ if(X&Y) continue; u64 Z=ALL&~(X|Y); if(!id.count(Z)) continue; cons.push_back({get(X),get(Y),get(Z)}); }
  }
  int V=sets.size(); printf("sets: %d constraints: %zu\n",V,cons.size());
  // union-find identifications
  par.resize(V); for(int i=0;i<V;i++) par[i]=i;
  function<int(int)> f=[&](int x){return par[x]==x?x:par[x]=f(par[x]);};
  for(auto&e:idents){ int a=f(e[0]),b=f(e[1]); if(a!=b) par[a]=b; }
  vector<int> cid(V,-1); int C=0; for(int i=0;i<V;i++){ int r=f(i); if(cid[r]<0) cid[r]=C++; }
  vector<vector<int>> cl;
  for(int c=0;c<C;c++){ vector<int> one; for(int x=0;x<q;x++) one.push_back(c*q+x+1); cl.push_back(one); for(int x=0;x<q;x++)for(int y=x+1;y<q;y++) cl.push_back({-(c*q+x+1),-(c*q+y+1)}); }
  set<array<int,3>> seen;
  for(auto&t:cons){ array<int,3> u={cid[f(t[0])],cid[f(t[1])],cid[f(t[2])]}; sort(u.begin(),u.end()); if(!seen.insert(u).second) continue;
    for(int x=0;x<q;x++)for(int y=0;y<q;y++)for(int z=0;z<q;z++){ if(u[0]==u[1]&&x!=y) continue; if(u[1]==u[2]&&y!=z) continue; if(lo(x,y,z)) continue;
      set<int> l={-(u[0]*q+x+1),-(u[1]*q+y+1),-(u[2]*q+z+1)}; cl.push_back(vector<int>(l.begin(),l.end())); } }
  sort(cl.begin(),cl.end()); cl.erase(unique(cl.begin(),cl.end()),cl.end());
  FILE*fo=fopen(argv[4],"w"); fprintf(fo,"p cnf %d %zu\n",C*q,cl.size()); for(auto&c:cl){for(int l:c) fprintf(fo,"%d ",l); fprintf(fo,"0\n");} fclose(fo);
  printf("classes %d, distinct constraints %zu, clauses %zu\n",C,seen.size(),cl.size());
}
