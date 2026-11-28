// W1: exact checks of the binary icosahedral frame in Q(sqrt5) quaternions.
// Checks: relations a^2=b^3=c^5=abc=-1; closure size 120; order statistics;
// Fourier/Schur identity (1/60) sum_g tr(h g) g^{-1} = h for h in {1,i,j,k};
// trace-pairing identity used for O(rho0)=1; words for i,j,k in a,b.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>
#include <string>
#include <numeric>
typedef long long ll;
struct Q { ll n, d; };
static Q mk(ll n, ll d){ if(d<0){n=-n;d=-d;} ll g=std::gcd(n<0?-n:n,d); if(g==0)g=1; return {n/g,d/g}; }
static Q add(Q a,Q b){ return mk(a.n*b.d+b.n*a.d,a.d*b.d);}
static Q mul(Q a,Q b){ return mk(a.n*b.n,a.d*b.d);}
static Q neg(Q a){ return {-a.n,a.d}; }
static bool eq(Q a,Q b){ return a.n==b.n&&a.d==b.d; }
struct R { Q x, y; }; // x + y sqrt5
static R radd(R a,R b){ return {add(a.x,b.x),add(a.y,b.y)}; }
static R rmul(R a,R b){ return {add(mul(a.x,b.x),mul(mk(5,1),mul(a.y,b.y))), add(mul(a.x,b.y),mul(a.y,b.x))}; }
static R rneg(R a){ return {neg(a.x),neg(a.y)}; }
static bool req(R a,R b){ return eq(a.x,b.x)&&eq(a.y,b.y); }
static R rq(ll n,ll d){ return {mk(n,d),mk(0,1)}; }
struct H { R c[4]; }; // c0 + c1 i + c2 j + c3 k
static H hmul(const H&p,const H&q){
  H r; const R *a=p.c,*b=q.c;
  r.c[0]=radd(radd(rmul(a[0],b[0]),rneg(rmul(a[1],b[1]))),radd(rneg(rmul(a[2],b[2])),rneg(rmul(a[3],b[3]))));
  r.c[1]=radd(radd(rmul(a[0],b[1]),rmul(a[1],b[0])),radd(rmul(a[2],b[3]),rneg(rmul(a[3],b[2]))));
  r.c[2]=radd(radd(rmul(a[0],b[2]),rneg(rmul(a[1],b[3]))),radd(rmul(a[2],b[0]),rmul(a[3],b[1])));
  r.c[3]=radd(radd(rmul(a[0],b[3]),rmul(a[1],b[2])),radd(rneg(rmul(a[2],b[1])),rmul(a[3],b[0])));
  return r; }
static H hconj(const H&p){ H r=p; for(int k=1;k<4;k++) r.c[k]=rneg(p.c[k]); return r; }
static bool heq(const H&p,const H&q){ for(int k=0;k<4;k++) if(!req(p.c[k],q.c[k])) return false; return true; }
static std::string key(const H&p){ char buf[512]; std::string s; for(int k=0;k<4;k++){ snprintf(buf,512,"%lld/%lld,%lld/%lld;",p.c[k].x.n,p.c[k].x.d,p.c[k].y.n,p.c[k].y.d); s+=buf;} return s; }
static H one(){ H r; for(int k=0;k<4;k++) r.c[k]=rq(0,1); r.c[0]=rq(1,1); return r; }
static H basis(int m){ H r; for(int k=0;k<4;k++) r.c[k]=rq(0,1); r.c[m]=rq(1,1); return r; }
static H hscale(const H&p,R s){ H r; for(int k=0;k<4;k++) r.c[k]=rmul(s,p.c[k]); return r; }
static H hadd(const H&p,const H&q){ H r; for(int k=0;k<4;k++) r.c[k]=radd(p.c[k],q.c[k]); return r; }
static void pr(const char*nm,const H&p){ printf("%s = ",nm); for(int k=0;k<4;k++) printf("(%lld/%lld + %lld/%lld s5)%s ",p.c[k].x.n,p.c[k].x.d,p.c[k].y.n,p.c[k].y.d, k==0?"":(k==1?"i":(k==2?"j":"k"))); printf("\n"); }
int main(){
  R phi={mk(1,2),mk(1,2)}, phiinv={mk(-1,2),mk(1,2)}, half=rq(1,2);
  H a; a.c[0]=rq(0,1); a.c[1]=rmul(half,phiinv); a.c[2]=rmul(half,phi); a.c[3]=half;
  H b; for(int k=0;k<4;k++) b.c[k]=half;
  H minus1=hscale(one(),rq(-1,1));
  H c=hscale(hmul(hconj(b),hconj(a)),rq(-1,1)); // c = -b^-1 a^-1 (unit quaternions: inverse = conjugate)
  pr("a",a); pr("b",b); pr("c",c);
  H a2=hmul(a,a), b3=hmul(hmul(b,b),b), c5=one(); for(int t=0;t<5;t++) c5=hmul(c5,c);
  H abc=hmul(hmul(a,b),c);
  printf("a^2=-1:%d b^3=-1:%d c^5=-1:%d abc=-1:%d\n",heq(a2,minus1),heq(b3,minus1),heq(c5,minus1),heq(abc,minus1));
  printf("tr c = 2Re c = %lld/%lld + %lld/%lld s5 (phi = 1/2+1/2 s5)\n", rmul(rq(2,1),c.c[0]).x.n, rmul(rq(2,1),c.c[0]).x.d, rmul(rq(2,1),c.c[0]).y.n, rmul(rq(2,1),c.c[0]).y.d);
  // closure with words
  std::vector<H> G; std::vector<std::string> W; std::map<std::string,int> idx;
  G.push_back(one()); W.push_back("1"); idx[key(one())]=0;
  for(size_t t=0;t<G.size();t++){
    H gens[2]={a,b}; const char* nm[2]={"a","b"};
    for(int s=0;s<2;s++){ H h=hmul(G[t],gens[s]); std::string kk=key(h); if(!idx.count(kk)){ idx[kk]=G.size(); G.push_back(h); W.push_back(W[t]=="1"?std::string(nm[s]):W[t]+nm[s]); } }
    if(G.size()>1000){ printf("closure exploded\n"); return 1; }
  }
  printf("|<a,b>| = %zu\n",G.size());
  // orders
  std::map<int,int> ord; for(auto&g:G){ H p=g; int o=1; while(!heq(p,one())){ p=hmul(p,g); o++; } ord[o]++; }
  for(auto&kv:ord) printf("order %d: %d elements\n",kv.first,kv.second);
  // i,j,k words
  const char* bn[4]={"1","i","j","k"};
  for(int m=1;m<4;m++){ auto it=idx.find(key(basis(m))); printf("%s in group: %s word=%s\n",bn[m], it!=idx.end()?"yes":"NO", it!=idx.end()?W[it->second].c_str():"-"); }
  // Fourier identity: (1/60) sum_g tr(h g) g^{-1} = h, tr(q)=2 Re q
  bool fok=true;
  for(int m=0;m<4;m++){ H h=basis(m); H S; for(int k=0;k<4;k++) S.c[k]=rq(0,1);
    for(auto&g:G){ R tr=rmul(rq(2,1),hmul(h,g).c[0]); S=hadd(S,hscale(hconj(g),tr)); }
    S=hscale(S,rq(1,60)); if(!heq(S,h)){ fok=false; pr("FAIL",S);} }
  printf("Fourier identity N_rho0(h)=h on basis: %s\n",fok?"OK":"FAIL");
  // O(rho0)_{nm} = -(1/120) sum_g tr(e_m g^-1) tr(e_n g) should be identity
  bool ook=true;
  for(int n=1;n<4;n++) for(int m=1;m<4;m++){ R s=rq(0,1); for(auto&g:G){ R t1=rmul(rq(2,1),hmul(basis(m),hconj(g)).c[0]); R t2=rmul(rq(2,1),hmul(basis(n),g).c[0]); s=radd(s,rmul(t1,t2)); } s=rmul(s,rq(-1,120)); if(!req(s,rq(n==m,1))) ook=false; }
  printf("O(rho0) = identity: %s\n",ook?"OK":"FAIL");
  // class sums of traces of other 2-dim rep (Galois conjugate): tr c'
  printf("Galois-conjugate trace of c: 1/2 - 1/2 s5 = 1-phi\n");
  return 0; }
