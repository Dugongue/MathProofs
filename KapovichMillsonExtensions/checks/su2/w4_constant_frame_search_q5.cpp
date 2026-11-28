// W4: constant frame for the W2 von Staudt gadgets from the 2I frame, exact over Q(sqrt5).
// Constant LINES: the 20 order-3 icosians P (line {v.p = 1/2} of Pi), minus P1^{+-1}.
// Constant POINTS: icosians g != -1 whose Cayley vector v = vec(g)/(1+re g) lies on Pi (v.n1 = 1/2),
// plus meets of two constant lines (pinned by Cramer).
// Search for (E; L,M through E; O,U on L; A; K = join(E,A); N through O) such that the W2 gadgets
// (projective form, E = infinity on L) are representable at the base and compute x+y, xy exactly.
// Representable: point finite, line not through T1 (origin of (s,t)), no degenerate join/meet.
// Coordinates: v = T1 + s e1 + t e2', e1=(1,-1,0), e2'=(1,1,-2)/6.
#include <cstdio>
#include <cstdlib>
#include <vector>
typedef __int128 I;
static I ab(I a){return a<0?-a:a;}
static I g(I a,I b){a=ab(a);b=ab(b);while(b){I t=a%b;a=b;b=t;}return a?a:1;}
struct Q{I n,d;};
static Q mk(I n,I d){if(d<0){n=-n;d=-d;}I k=g(n,d);return {n/k,d/k};}
static Q qa(Q a,Q b){return mk(a.n*b.d+b.n*a.d,a.d*b.d);}
static Q qs(Q a,Q b){return mk(a.n*b.d-b.n*a.d,a.d*b.d);}
static Q qm(Q a,Q b){return mk(a.n*b.n,a.d*b.d);}
static Q qd(Q a,Q b){return mk(a.n*b.d,a.d*b.n);}
static Q R(long n,long d=1){return mk(n,d);}
struct F{Q a,b;}; // a + b sqrt5
static F f(Q a,Q b){return {a,b};}
static F fr(long n,long d=1){return {R(n,d),R(0)};}
static F add(F x,F y){return {qa(x.a,y.a),qa(x.b,y.b)};}
static F sub(F x,F y){return {qs(x.a,y.a),qs(x.b,y.b)};}
static F mul(F x,F y){return {qa(qm(x.a,y.a),qm(R(5),qm(x.b,y.b))),qa(qm(x.a,y.b),qm(x.b,y.a))};}
static bool z(F x){return x.a.n==0&&x.b.n==0;}
static F inv(F x){Q n=qs(qm(x.a,x.a),qm(R(5),qm(x.b,x.b))); return {qd(x.a,n),qd(mk(-x.b.n,x.b.d),n)};}
static F dv(F x,F y){return mul(x,inv(y));}
static bool eq(F x,F y){return z(sub(x,y));}
static bool big(F x){I B=(I)1000000; return ab(x.a.n)>B||x.a.d>B||ab(x.b.n)>B||x.b.d>B;}
struct H{F c[3];};
static H cross(H u,H v){H r;r.c[0]=sub(mul(u.c[1],v.c[2]),mul(u.c[2],v.c[1]));r.c[1]=sub(mul(u.c[2],v.c[0]),mul(u.c[0],v.c[2]));r.c[2]=sub(mul(u.c[0],v.c[1]),mul(u.c[1],v.c[0]));return r;}
static F dot(H u,H v){return add(add(mul(u.c[0],v.c[0]),mul(u.c[1],v.c[1])),mul(u.c[2],v.c[2]));}
static H sc(F k,H u){H r;for(int i=0;i<3;i++)r.c[i]=mul(k,u.c[i]);return r;}
static H ad(H u,H v){H r;for(int i=0;i<3;i++)r.c[i]=add(u.c[i],v.c[i]);return r;}
static bool deg(H u){return z(u.c[0])&&z(u.c[1])&&z(u.c[2]);}
static H nrm(H u){for(int i=2;i>=0;i--) if(!z(u.c[i])) return sc(inv(u.c[i]),u); return u;}
static bool same(H a,H b){return deg(cross(a,b));}
static bool okP(H P){return !deg(P)&&!z(P.c[2]);}
static bool okL(H l){return !deg(l)&&!z(l.c[2]);}
static bool bigH(H u){for(int i=0;i<3;i++) if(big(u.c[i])) return true; return false;}
static bool good;
static H J(H P,H Q2){H l=cross(P,Q2); if(!okL(l)) good=false; return l;}
static H M_(H l,H m){H P=cross(l,m); if(!okP(P)) good=false; return P;}
static void pf(F x){printf("(%lld/%lld + %lld/%lld r5)",(long long)x.a.n,(long long)x.a.d,(long long)x.b.n,(long long)x.b.d);}
int main(){
  F phi=f(R(1,2),R(1,2)), phii=f(R(-1,2),R(1,2));
  std::vector<std::vector<F>> ico;
  for(int m=0;m<4;m++)for(int sgn=-1;sgn<=1;sgn+=2){std::vector<F> q(4,fr(0)); q[m]=fr(sgn); ico.push_back(q);}
  for(int a=-1;a<=1;a+=2)for(int b=-1;b<=1;b+=2)for(int c=-1;c<=1;c+=2)for(int d=-1;d<=1;d+=2) ico.push_back({fr(a,2),fr(b,2),fr(c,2),fr(d,2)});
  int ev[12][4]={{0,1,2,3},{0,2,3,1},{0,3,1,2},{1,0,3,2},{1,2,0,3},{1,3,2,0},{2,0,1,3},{2,1,3,0},{2,3,0,1},{3,0,2,1},{3,1,0,2},{3,2,1,0}};
  F base[4]={fr(0),fr(1),phii,phi};
  for(int p=0;p<12;p++)for(int s1=-1;s1<=1;s1+=2)for(int s2=-1;s2<=1;s2+=2)for(int s3=-1;s3<=1;s3+=2){
    std::vector<F> q(4); F vals[4]={base[0],mul(fr(s1),base[1]),mul(fr(s2),base[2]),mul(fr(s3),base[3])};
    for(int m=0;m<4;m++) q[ev[p][m]]=mul(fr(1,2),vals[m]);
    ico.push_back(q);
  }
  // sanity: all unit norm
  int nonunit=0; for(auto&q:ico){F n=fr(0); for(int m=0;m<4;m++) n=add(n,mul(q[m],q[m])); if(!eq(n,fr(1))) nonunit++;}
  printf("icosians: %zu (non-unit %d)\n",ico.size(),nonunit);
  F e1[3]={fr(1),fr(-1),fr(0)}, e2[3]={fr(1,6),fr(1,6),fr(-2,6)};
  F n1[3]={fr(1,2),fr(1,2),fr(1,2)}, T1[3]={fr(1,3),fr(1,3),fr(1,3)};
  auto d3=[&](F*a,F*b){return add(add(mul(a[0],b[0]),mul(a[1],b[1])),mul(a[2],b[2]));};
  std::vector<H> Ls,Ps; int nIcoPts=0;
  for(auto&q:ico){
    F p[3]={q[1],q[2],q[3]};
    if(eq(q[0],fr(-1,2))){
      if(eq(d3(p,n1),fr(3,4))||eq(d3(p,n1),fr(-3,4))) continue;
      H l={{d3(p,e1),d3(p,e2),sub(d3(p,T1),fr(1,2))}}; if(!okL(l)) continue; Ls.push_back(nrm(l));
    }
    if(!eq(q[0],fr(-1))){ F den=add(fr(1),q[0]); F v[3]={dv(p[0],den),dv(p[1],den),dv(p[2],den)};
      if(eq(d3(v,n1),fr(1,2))){ F w[3]={sub(v[0],T1[0]),sub(v[1],T1[1]),sub(v[2],T1[2])};
        H P={{dv(d3(w,e1),fr(2)),dv(d3(w,e2),fr(1,6)),fr(1)}}; bool dup=false; for(auto&X:Ps) if(same(X,P)) dup=true; if(!dup){Ps.push_back(P);nIcoPts++;}} }
  }
  printf("constant lines %zu, constant icosian points %d\n",Ls.size(),nIcoPts);
  { std::vector<H> nP=Ps;
    for(size_t i=0;i<Ls.size();i++)for(size_t j=i+1;j<Ls.size();j++){H P=cross(Ls[i],Ls[j]); if(!okP(P)) continue; P=nrm(P); if(bigH(P)) continue; bool dup=false; for(auto&X:nP) if(same(X,P)){dup=true;break;} if(!dup) nP.push_back(P);}
    Ps=nP; printf("after meets: %zu points\n",Ps.size()); }
  srand(5);
  int found=0;
  for(size_t e=0;e<Ps.size()&&!found;e++){
    H E=Ps[e];
    std::vector<int> thr; for(size_t i=0;i<Ls.size();i++) if(z(dot(Ls[i],E))) thr.push_back(i);
    if(thr.size()<2) continue;
    for(size_t a1=0;a1<thr.size()&&!found;a1++)for(size_t a2=0;a2<thr.size()&&!found;a2++){ if(a1==a2) continue;
      H L=Ls[thr[a1]], Mm=Ls[thr[a2]];
      std::vector<int> onL; for(size_t i=0;i<Ps.size();i++) if(z(dot(L,Ps[i]))&&!same(Ps[i],E)) onL.push_back(i);
      if(onL.size()<2) continue;
      for(size_t o=0;o<onL.size()&&!found;o++){ H O=Ps[onL[o]];
        int ni=-1; for(size_t i=0;i<Ls.size();i++) if(z(dot(Ls[i],O))&&!same(Ls[i],L)){ni=i;break;}
        if(ni<0) continue; H N=Ls[ni];
        for(size_t u=0;u<onL.size()&&!found;u++){ if(o==u) continue; H U=Ps[onL[u]];
        for(size_t ai=0;ai<Ps.size()&&!found;ai++){ H A=Ps[ai];
          if(z(dot(L,A))||z(dot(Mm,A))) continue;
          good=true; H K=J(E,A); H OA=J(O,A), UA=J(U,A); H U1=M_(OA,Mm), U3=M_(UA,Mm); if(!good) continue;
          int i0=-1,i1=-1; for(int p=0;p<3&&i0<0;p++)for(int q=p+1;q<3;q++){ if(!z(sub(mul(O.c[p],E.c[q]),mul(O.c[q],E.c[p])))){i0=p;i1=q;break;} }
          auto coord=[&](H P,bool&okc)->F{ F det=sub(mul(O.c[i0],E.c[i1]),mul(O.c[i1],E.c[i0]));
            F al=dv(sub(mul(P.c[i0],E.c[i1]),mul(P.c[i1],E.c[i0])),det);
            F be=dv(sub(mul(O.c[i0],P.c[i1]),mul(O.c[i1],P.c[i0])),det);
            okc=!z(al); return okc?dv(be,al):fr(0); };
          bool okc; F xu=coord(U,okc); if(!okc||z(xu)) continue;
          auto pt=[&](F x)->H{ return ad(O,sc(mul(x,xu),E)); };
          H b_lY,b_B,b_lX,b_U2,b_lB,b_l1,b_C,b_l2,b_U4,b_l3;
          { H X=pt(fr(0)),Y=pt(fr(0)); b_lY=J(Y,U1); b_B=M_(b_lY,K); b_lX=J(A,X); b_U2=M_(b_lX,Mm); b_lB=J(b_B,b_U2); H Z=M_(b_lB,L); if(good){bool k; F v=coord(Z,k); if(!k||!z(v)) good=false;} }
          { H X=pt(fr(0)),Y=pt(fr(0)); b_l1=J(X,U3); b_C=M_(b_l1,OA); b_l2=J(A,Y); b_U4=M_(b_l2,Mm); b_l3=J(b_C,b_U4); H Z=M_(b_l3,L); if(good){bool k; F v=coord(Z,k); if(!k||!z(v)) good=false;} }
          if(!good) continue;
          int bad=0,tests=0;
          for(int it=0;it<40;it++){ F x=fr(rand()%11-5,rand()%3+1), y=fr(rand()%11-5,rand()%3+1);
            H X=pt(x),Y=pt(y);
            H B=cross(cross(Y,U1),K), U2=cross(cross(A,X),Mm); H Z=cross(cross(B,U2),L);
            H C=cross(cross(X,U3),OA), U4=cross(cross(A,Y),Mm); H Z2=cross(cross(C,U4),L);
            if(deg(Z)||deg(Z2)) continue; bool k1,k2; F v1=coord(Z,k1), v2=coord(Z2,k2); if(!k1||!k2) continue;
            tests++; if(!eq(v1,add(x,y))||!eq(v2,mul(x,y))) bad++; }
          if(bad||tests<30) continue;
          found++;
          auto P2=[&](const char*n,H P){P=nrm(P); printf("  %s = (",n); pf(P.c[0]); printf(", "); pf(P.c[1]); printf(")\n");};
          auto L2=[&](const char*n,H l){l=nrm(l); printf("  %s : ",n); pf(l.c[0]); printf(" s + "); pf(l.c[1]); printf(" t + 1 = 0\n");};
          printf("FRAME found (value tests %d, 0 bad; all base joins/meets representable)\n",tests);
          P2("E",E); L2("L",L); L2("M",Mm); L2("K",K); P2("O",O); P2("U",U); P2("A",A); L2("N",N);
          P2("U1",U1); P2("U3",U3); L2("base lY",b_lY); P2("base B",b_B); L2("base lX",b_lX); P2("base U2",b_U2); L2("base lB",b_lB);
          L2("base l1",b_l1); P2("base C",b_C); L2("base l2",b_l2); P2("base U4",b_U4); L2("base l3",b_l3);
          for(int q=0;q<4;q++){ H P = q==0?E:(q==1?O:(q==2?U:A)); int cnt=0; for(auto&l:Ls) if(z(dot(l,P))) cnt++; printf("  constant point %d lies on %d constant lines\n",q,cnt);}
          { int cnt=0; for(auto&l:Ls) if(same(l,K)) cnt++; printf("  K is a constant icosian line: %d (else K = join(E,A), representable)\n",cnt);}
        }}
      }
    }
  }
  printf("found=%d\n",found);
  return found?0:1;
}
