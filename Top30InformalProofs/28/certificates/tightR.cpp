// Restricted (UNSAT-sound) encoding of the CYCLE_3[L]-loop condition in Pol(R, NAE_q) (or LO_q),
// R a ternary relation on [a] given as words. f : [a]^n -> [q], n = 3L.
// Identified vectors u_k(x) = x∘c_k (x : Z_L -> [a]). Family: level0 = all u_k(x);
// constraints: for X,Y in level0 (or level0 + generated), every Z with (X_i,Y_i,Z_i) in R for all i,
// enumerated if the number of free columns is <= cap. Rows (X,Y,Z) must map into B.
// usage: tightR L q NAE|LO cap rounds out.cnf word...
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <array>
#include <map>
#include <set>
#include <string>
#include <algorithm>
#include <functional>
using namespace std;
int L,q,a,n,cap,rounds; bool LO;
vector<array<int,3>> R;
bool okB(int x,int y,int z){ if(LO){int m=max(x,max(y,z)); return (x==m)+(y==m)+(z==m)==1;} return !(x==y&&y==z); }
int main(int argc,char**argv){
  L=atoi(argv[1]); q=atoi(argv[2]); LO=!strcmp(argv[3],"LO"); cap=atoi(argv[4]); rounds=atoi(argv[5]); const char*out=argv[6];
  a=0; for(int i=7;i<argc;i++){ array<int,3> t={argv[i][0]-'0',argv[i][1]-'0',argv[i][2]-'0'}; for(int k=0;k<3;k++) a=max(a,t[k]+1); R.push_back(t); }
  n=3*L;
  vector<array<int,3>> H; for(int t=0;t<L;t++){int x0=t,x1=(t+1)%L,x2=(t+2)%L; H.push_back({x0,x1,x2}); H.push_back({x1,x2,x0}); H.push_back({x2,x0,x1});}
  map<string,int> id; vector<string> vecs;
  auto get=[&](const string&s){ auto it=id.find(s); if(it!=id.end()) return it->second; int k=vecs.size(); id[s]=k; vecs.push_back(s); return k; };
  vector<array<int,2>> idents; vector<int> lvl0;
  long long NX=1; for(int i=0;i<L;i++) NX*=a;
  for(long long c=0;c<NX;c++){ vector<int> x(L); long long cc=c; for(int i=0;i<L;i++){x[i]=cc%a;cc/=a;}
    int ix[3]; for(int k=0;k<3;k++){ string s(n,'0'); for(int h=0;h<n;h++) s[h]='0'+x[H[h][k]]; ix[k]=get(s); lvl0.push_back(ix[k]); }
    idents.push_back({ix[0],ix[1]}); idents.push_back({ix[0],ix[2]}); }
  { int sm=getenv("SMALL")?atoi(getenv("SMALL")):0; // add vectors with <= sm nonzero entries
    function<void(string&,int,int)> gen=[&](string&s,int pos,int left){ if(pos==n){ lvl0.push_back(get(s)); return; }
      gen(s,pos+1,left); if(left>0) for(int v=1;v<a;v++){ s[pos]='0'+v; gen(s,pos+1,left-1); s[pos]='0'; } };
    if(sm>0){ string s(n,'0'); gen(s,0,sm); } }
  sort(lvl0.begin(),lvl0.end()); lvl0.erase(unique(lvl0.begin(),lvl0.end()),lvl0.end());
  // third-entry table
  vector<vector<vector<int>>> third(a,vector<vector<int>>(a));
  for(auto&t:R) third[t[0]][t[1]].push_back(t[2]);
  set<array<int,3>> cons;
  vector<int> pool=lvl0;
  for(int r=0;r<rounds;r++){
    vector<int> P=pool; size_t before=vecs.size();
    for(int i:P) for(int j:lvl0){ const string X=vecs[i], Y=vecs[j]; vector<int> freeCols; bool okc=true; string Z(n,'0');
      for(int h=0;h<n;h++){ auto&o=third[X[h]-'0'][Y[h]-'0']; if(o.empty()){okc=false;break;} if(o.size()==1) Z[h]='0'+o[0]; else freeCols.push_back(h); }
      if(!okc||(int)freeCols.size()>cap) continue;
      // enumerate choices
      function<void(int)> rec=[&](int k){ if(k==(int)freeCols.size()){ int z=get(Z); cons.insert({id[X],id[Y],z}); return; }
        int h=freeCols[k]; for(int v:third[X[h]-'0'][Y[h]-'0']){ Z[h]='0'+v; rec(k+1);} };
      rec(0); }
    for(size_t k=before;k<vecs.size();k++) pool.push_back(k);
    printf("round %d: vectors %zu constraints %zu\n",r,vecs.size(),cons.size()); fflush(stdout);
  }
  int V=vecs.size(); vector<int> par(V); for(int i=0;i<V;i++) par[i]=i;
  function<int(int)> f=[&](int x){return par[x]==x?x:par[x]=f(par[x]);};
  for(auto&e:idents){int x=f(e[0]),y=f(e[1]); if(x!=y) par[x]=y;}
  vector<int> cid(V,-1); int C=0; for(int i=0;i<V;i++){int r=f(i); if(cid[r]<0) cid[r]=C++;}
  vector<vector<int>> cl;
  for(int c=0;c<C;c++){ vector<int> one; for(int x=0;x<q;x++) one.push_back(c*q+x+1); cl.push_back(one); for(int x=0;x<q;x++)for(int y=x+1;y<q;y++) cl.push_back({-(c*q+x+1),-(c*q+y+1)}); }
  set<array<int,3>> seen;
  for(auto&t:cons){ array<int,3> u={cid[f(t[0])],cid[f(t[1])],cid[f(t[2])]}; sort(u.begin(),u.end()); if(!seen.insert(u).second) continue;
    for(int x=0;x<q;x++)for(int y=0;y<q;y++)for(int z=0;z<q;z++){ if(u[0]==u[1]&&x!=y) continue; if(u[1]==u[2]&&y!=z) continue; if(okB(x,y,z)) continue;
      set<int> l={-(u[0]*q+x+1),-(u[1]*q+y+1),-(u[2]*q+z+1)}; cl.push_back(vector<int>(l.begin(),l.end())); } }
  sort(cl.begin(),cl.end()); cl.erase(unique(cl.begin(),cl.end()),cl.end());
  FILE*fo=fopen(out,"w"); fprintf(fo,"p cnf %d %zu\n",C*q,cl.size()); for(auto&c:cl){for(int l:c) fprintf(fo,"%d ",l); fprintf(fo,"0\n");} fclose(fo);
  printf("classes %d distinct constraints %zu clauses %zu\n",C,seen.size(),cl.size());
}
