// Minimal RUP checker for (D)RAT proofs from CaDiCaL (text DRAT). Deletions are ignored (sound for RUP).
// Each added lemma must follow by unit propagation from formula + earlier lemmas; final empty clause required.
// usage: rupcheck formula.cnf proof.drat
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <cstring>
using namespace std;
int nv; vector<vector<int>> C; vector<vector<int>> W; // watches: index by lit code
vector<signed char> val; vector<int> trail;
inline int code(int l){return l>0?2*l:2*(-l)+1;}
inline int V(int l){ int v=val[abs(l)]; return l>0?v:-v; } // 1 true, -1 false, 0 unassigned
bool assign(int l){ int v=V(l); if(v==1) return true; if(v==-1) return false; val[abs(l)]=l>0?1:-1; trail.push_back(l); return true; }
void addClause(vector<int> c){
  int id=C.size(); C.push_back(c);
  if(c.size()>=2){ W[code(c[0])].push_back(id); W[code(c[1])].push_back(id); }
}
// propagate from trail position; returns false on conflict
bool propagate(size_t qh){
  while(qh<trail.size()){ int l=trail[qh++]; int fl=-l; auto&ws=W[code(fl)];
    for(size_t i=0;i<ws.size();){ int id=ws[i]; auto&c=C[id];
      if(c[0]==fl) swap(c[0],c[1]);
      if(V(c[0])==1){ i++; continue; }
      bool moved=false; for(size_t k=2;k<c.size();k++) if(V(c[k])!=-1){ swap(c[1],c[k]); W[code(c[1])].push_back(id); ws[i]=ws.back(); ws.pop_back(); moved=true; break; }
      if(moved) continue;
      if(V(c[0])==-1) return false;
      if(V(c[0])==0) assign(c[0]);
      i++; }
  }
  return true;
}
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); char buf[256]; int ncl;
  while(fscanf(f," %255s",buf)==1){ if(buf[0]=='c'){ int ch; while((ch=fgetc(f))!='\n'&&ch!=EOF); continue;} if(buf[0]=='p'){ fscanf(f,"%*s %d %d",&nv,&ncl); break; } }
  val.assign(nv+1,0); W.assign(2*nv+2,{});
  vector<int> units; vector<int> cur; int x;
  while(fscanf(f,"%d",&x)==1){ if(x==0){ if(cur.size()==1) units.push_back(cur[0]); else if(cur.empty()){ printf("empty clause in formula\n"); return 0;} else addClause(cur); cur.clear(); } else cur.push_back(x); }
  fclose(f);
  // top-level units
  bool conflict=false; for(int u:units) if(!assign(u)) conflict=true;
  if(!conflict && !propagate(0)) conflict=true;
  size_t topq=trail.size();
  if(conflict){ printf("formula refuted by unit propagation alone: VERIFIED UNSAT\n"); return 0; }
  FILE*p=fopen(argv[2],"r"); long long lemmas=0; bool del=false; bool gotEmpty=false;
  cur.clear(); int c;
  while(true){ int ch=fgetc(p); if(ch==EOF) break; if(ch=='d'){ del=true; continue; } if(ch==' '||ch=='\n'||ch=='\r') continue; ungetc(ch,p);
    if(fscanf(p,"%d",&x)!=1) break;
    if(x!=0){ cur.push_back(x); continue; }
    if(del){ del=false; cur.clear(); continue; }
    lemmas++;
    // RUP check: assign negations
    size_t mark=trail.size(); bool confl=false;
    for(int l:cur){ if(!assign(-l)){ confl=true; break; } }
    if(!confl) confl=!propagate(mark);
    // undo
    while(trail.size()>mark){ val[abs(trail.back())]=0; trail.pop_back(); }
    if(!confl){ printf("lemma %lld NOT RUP: FAILED\n",lemmas); return 1; }
    if(cur.empty()){ gotEmpty=true; break; }
    if(cur.size()==1){ assign(cur[0]); if(!propagate(trail.size()-1)){ gotEmpty=true; break; } topq=trail.size(); }
    else addClause(cur);
    cur.clear(); }
  printf("lemmas checked %lld, empty clause %s\n",lemmas,gotEmpty?"derived: VERIFIED UNSAT":"NOT derived: FAILED");
}
