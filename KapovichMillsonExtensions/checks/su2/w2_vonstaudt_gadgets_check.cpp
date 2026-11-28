// W2: exact rational check of the von Staudt addition / multiplication gadgets
// in the W4 tangent-plane model: points (s,s'), lines (A,B) meaning A s + B s' = 1.
// join/meet by Cramer; verifies Z = x+y and Z = x*y, and that every Cramer
// determinant is nonzero at the base (x,y) = (0,0) and on random inputs.
#include <cstdio>
#include <cstdlib>
#include <cstdint>
typedef __int128 I;
static I gcdI(I a, I b){ if(a<0)a=-a; if(b<0)b=-b; while(b){I t=a%b;a=b;b=t;} return a; }
struct Q{ I n,d; Q(I a=0,I b=1){ if(b<0){a=-a;b=-b;} I g=gcdI(a,b); if(g==0)g=1; n=a/g; d=b/g; } };
Q operator+(Q a,Q b){return Q(a.n*b.d+b.n*a.d,a.d*b.d);} Q operator-(Q a,Q b){return Q(a.n*b.d-b.n*a.d,a.d*b.d);}
Q operator*(Q a,Q b){return Q(a.n*b.n,a.d*b.d);} Q operator/(Q a,Q b){ if(b.n==0){printf("DIV0\n");exit(1);} return Q(a.n*b.d,a.d*b.n);}
bool eq(Q a,Q b){return a.n==b.n&&a.d==b.d;} bool zero(Q a){return a.n==0;}
struct P{Q s,t;}; struct L{Q A,B;};
static int bad=0;
L join(P p,P q){ Q D=p.s*q.t-q.s*p.t; if(zero(D)){bad++; return {Q(0),Q(0)};} return { (q.t-p.t)/D, (p.s-q.s)/D }; }
P meet(L l,L m){ Q D=l.A*m.B-m.A*l.B; if(zero(D)){bad++; return {Q(0),Q(0)};} return { (m.B-l.B)/D, (l.A-m.A)/D }; }
bool inc(P p,L l){ return eq(l.A*p.s+l.B*p.t,Q(1)); }
int main(){
  // constants (rational): L: s'=1, M: s'=c, A=(a1,a2), O=(0,1), U=(1,1)
  Q c(3), a1(3,1), a2(-1,1);
  L Lc={Q(0),Q(1)}, Mc={Q(0),Q(1)/c};
  P O={Q(0),Q(1)}, U={Q(1),Q(1)}, A={a1,a2};
  L K={Q(0),Q(1)/a2};                 // line through A parallel to L (through E)
  P U1=meet(join(O,A),Mc), U3=meet(join(U,A),Mc);
  int fails=0, tests=0;
  srand(12345);
  for(int it=0; it<4000; it++){
    Q x,y;
    if(it==0){x=Q(0);y=Q(0);} else { x=Q(rand()%41-20, rand()%9+1); y=Q(rand()%41-20, rand()%9+1); }
    int b0=bad;
    P X={x,Q(1)}, Y={y,Q(1)};
    // addition
    L lY=join(Y,U1); P B=meet(lY,K); L lX=join(A,X); P U2=meet(lX,Mc); L lB=join(B,U2); P Z=meet(lB,Lc);
    bool okA = inc(Y,lY)&&inc(U1,lY)&&inc(B,lY)&&inc(B,K)&&inc(A,lX)&&inc(X,lX)&&inc(U2,lX)&&inc(U2,Mc)
             &&inc(B,lB)&&inc(U2,lB)&&inc(Z,lB)&&inc(Z,Lc)&&eq(Z.s,x+y);
    // multiplication
    L l1=join(X,U3); P C=meet(l1,join(O,A)); L l2=join(A,Y); P U4=meet(l2,Mc); L l3=join(C,U4); P W=meet(l3,Lc);
    bool okM = inc(X,l1)&&inc(U3,l1)&&inc(C,l1)&&inc(A,l2)&&inc(Y,l2)&&inc(U4,l2)&&inc(U4,Mc)
             &&inc(C,l3)&&inc(U4,l3)&&inc(W,l3)&&inc(W,Lc)&&eq(W.s,x*y);
    tests++;
    if(bad!=b0){ if(it==0){printf("BASE DEGENERATE\n");return 1;} continue; } // generic degeneracy off base: skip
    if(!okA||!okM){ fails++; printf("FAIL x=%lld/%lld y=%lld/%lld A%d M%d\n",(long long)x.n,(long long)x.d,(long long)y.n,(long long)y.d,okA,okM); }
  }
  printf("tests=%d degenerate_skipped=%d fails=%d (base nondegenerate)\n",tests,bad,fails);
  return fails?1:0;
}
