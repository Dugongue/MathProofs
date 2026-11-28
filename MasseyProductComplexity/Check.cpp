// Audit check for R-massey-main.md Theorem 2 (group side, after Lemma D).
// Independent of Lemma K: relators are evaluated as actual 5x5 matrix words.
// For random small systems S over F_p (N<=2 variables, 1..3 equations of types
// x_i+x_j=x_l, x_i*x_j=x_l, x_i=1) and random s,t,u,v in U_5(F_p) with
// superdiagonals e1..e4, decide by brute force whether there exist
// X_1..X_N, X'_1..X'_N in U_5(F_p) with zero superdiagonal satisfying all
// relators (R1),(R2),(R+),(R x),(R1c), and compare with brute-force solvability of S.
#include <cstdio>
#include <random>
#include <vector>
typedef long long ll;
static int P;
struct M { int a[5][5]; };
static M I(){ M m; for(int i=0;i<5;i++)for(int j=0;j<5;j++)m.a[i][j]=(i==j); return m; }
static M mul(const M&x,const M&y){ M m; for(int i=0;i<5;i++)for(int j=0;j<5;j++){ int s=0; for(int k=0;k<5;k++) s+=x.a[i][k]*y.a[k][j]; m.a[i][j]=((s%P)+P)%P;} return m; }
static M inv(const M&x){ // solve x*y=I by back substitution (upper unitriangular)
  M y=I(); for(int j=0;j<5;j++) for(int i=j-1;i>=0;i--){ int s=0; for(int k=i+1;k<=j;k++) s+=x.a[i][k]*y.a[k][j]; y.a[i][j]=(((-s)%P)+P)%P; } return y; }
static M comm(const M&x,const M&y){ return mul(mul(x,y),mul(inv(x),inv(y))); }
static bool isI(const M&x){ M e=I(); for(int i=0;i<5;i++)for(int j=0;j<5;j++) if(x.a[i][j]!=e.a[i][j]) return false; return true; }
static std::mt19937 rng(77);
struct Eq{ int type,i,j,l; }; // 0 add,1 mul,2 one
int main(){
  int pr[2]={2,3}; ll mism=0, tests=0, yes=0;
  for(int pi=0;pi<2;pi++){ P=pr[pi];
    std::vector<M> G; int pos[6][2]={{0,2},{1,3},{2,4},{0,3},{1,4},{0,4}}; int n=1; for(int q=0;q<6;q++) n*=P;
    for(int c=0;c<n;c++){ M m=I(); int x=c; for(int q=0;q<6;q++){ m.a[pos[q][0]][pos[q][1]]=x%P; x/=P;} G.push_back(m); }
    int reps = (P==2)? 60 : 40;
    for(int rep=0;rep<reps;rep++){
      int N = (P==2)? 1+rng()%2 : 1;
      int ne = 1+rng()%3; std::vector<Eq> S;
      for(int e=0;e<ne;e++){ Eq q; q.type=rng()%3; q.i=rng()%N; q.j=rng()%N; q.l=rng()%N; S.push_back(q); }
      // brute-force solvability
      bool solv=false; int tot=1; for(int v=0;v<N;v++) tot*=P;
      for(int c=0;c<tot&&!solv;c++){ int x[2]={c%P,(c/P)%P}; bool ok=true;
        for(auto&q:S){ if(q.type==0) ok&=((x[q.i]+x[q.j])%P==x[q.l]); else if(q.type==1) ok&=((x[q.i]*x[q.j])%P==x[q.l]); else ok&=(x[q.i]==1); }
        solv=ok; }
      // random s,t,u,v
      auto rU=[&](int k){ M m=I(); for(int i=0;i<5;i++)for(int j=i+1;j<5;j++) m.a[i][j]=(j==i+1)?(i==k):(int)(rng()%P); return m; };
      M s=rU(0),t=rU(1),u=rU(2),v=rU(3); M k1=comm(s,t),k2=comm(u,v), k1i=inv(k1);
      // candidates for X_i: [X,k1]=1 ; X'_i: [X',k2]=1  (relator R1, evaluated directly)
      std::vector<int> cX,cXp; for(int i=0;i<n;i++){ if(isI(comm(G[i],k1))) cX.push_back(i); if(isI(comm(G[i],k2))) cXp.push_back(i); }
      // pairs (X,X') satisfying R2: [X,k2]*[k1,X']^{-1}=1
      std::vector<std::pair<int,int>> pairs; for(int a:cX) for(int b:cXp) if(isI(mul(comm(G[a],k2),inv(comm(k1,G[b]))))) pairs.push_back({a,b});
      bool found=false; size_t np=pairs.size(); size_t lim = (N==1)? np : np*np;
      for(size_t c=0;c<lim&&!found;c++){ int X[2],Xp[2]; X[0]=pairs[c%np].first; Xp[0]=pairs[c%np].second; if(N==2){ X[1]=pairs[c/np].first; Xp[1]=pairs[c/np].second; }
        bool ok=true;
        for(auto&q:S){ if(!ok) break;
          if(q.type==0){ M w=mul(mul(G[X[q.i]],G[X[q.j]]),inv(G[X[q.l]])); ok=isI(comm(w,k2)); }
          else if(q.type==1){ ok=isI(mul(comm(G[X[q.i]],G[Xp[q.j]]),inv(comm(G[X[q.l]],k2)))); }
          else { ok=isI(comm(mul(G[X[q.i]],k1i),k2)); } }
        found=ok; }
      tests++; if(found!=solv){ mism++; printf("MISMATCH P=%d rep=%d solv=%d found=%d\n",P,rep,(int)solv,(int)found);} if(solv) yes++;
    }
  }
  printf("tests=%lld solvable=%lld mismatches=%lld\n",tests,yes,mism);
  printf(mism? "RESULT: FAIL\n":"RESULT: PASS\n"); return mism?1:0;
}
