// W4: exact rational check of the tangent-plane line lemma and incidence equivalence.
// Quaternions as (x0, x1, x2, x3); <X,Z> = x0 z0 + x.z ; tr(X Z^-1) = 2<X,Z> for det Z = 1.
#include <cstdio>
#include <cstdlib>
#include <numeric>
typedef __int128 I;
struct Q { I n, d; };
static I ab(I a){return a<0?-a:a;}
static I g(I a, I b){a=ab(a);b=ab(b);while(b){I t=a%b;a=b;b=t;}return a?a:1;}
static Q mk(I n, I d){ if(d<0){n=-n;d=-d;} I k=g(n,d); return {n/k,d/k}; }
static Q add(Q a,Q b){return mk(a.n*b.d+b.n*a.d,a.d*b.d);}
static Q sub(Q a,Q b){return mk(a.n*b.d-b.n*a.d,a.d*b.d);}
static Q mul(Q a,Q b){return mk(a.n*b.n,a.d*b.d);}
static Q dv(Q a,Q b){return mk(a.n*b.d,a.d*b.n);}
static Q R(long n,long d=1){return mk(n,d);}
static bool eq(Q a,Q b){return a.n==b.n&&a.d==b.d;}
struct V3{Q c[3];};
static Q dot(V3 a,V3 b){return add(add(mul(a.c[0],b.c[0]),mul(a.c[1],b.c[1])),mul(a.c[2],b.c[2]));}
static V3 lin(Q a,V3 x,Q b,V3 y){V3 r; for(int m=0;m<3;m++) r.c[m]=add(mul(a,x.c[m]),mul(b,y.c[m])); return r;}
int main(){
  V3 n1={{R(1,2),R(1,2),R(1,2)}}, e1={{R(1),R(-1),R(0)}}, e2={{R(1),R(1),R(-2)}};
  V3 T1=lin(R(2,3),n1,R(0),n1);
  int bad=0, tests=0;
  srand(12345);
  for(int it=0; it<2000; it++){
    Q A=R(rand()%41-20, rand()%9+1), B=R(rand()%41-20, rand()%9+1);
    // kappa = 3/(3 + A^2/2 + B^2/6)
    Q den=add(R(3),add(mul(R(1,2),mul(A,A)),mul(R(1,6),mul(B,B))));
    Q kap=dv(R(3),den);
    Q a=sub(R(1),mul(R(2),kap)), al=mul(kap,mul(A,R(1,2))), be=mul(kap,mul(B,R(1,6)));
    V3 p=lin(a,n1,al,e1); p=lin(R(1),p,be,e2);
    Q p0=R(-1,2);
    // det P = p0^2 + q(p) must be 1
    if(!eq(add(mul(p0,p0),dot(p,p)),R(1))) {bad++; printf("detP fail\n");}
    // gamma back = (1-a)/2 must equal kappa, and A,B recovered
    Q gam=mul(sub(R(1),a),R(1,2));
    if(!eq(gam,kap)) {bad++; printf("gamma fail\n");}
    if(!eq(dv(dot(e1,p),gam),A) || !eq(dv(dot(e2,p),gam),B)) {bad++; printf("AB fail\n");}
    // a point on the line: choose s, solve s' from A s + B s' = 1 (B != 0)
    if(B.n==0) continue;
    for(int k=0;k<3;k++){
      Q s=R(rand()%21-10, rand()%5+1);
      Q sp=dv(sub(R(1),mul(A,s)),B);
      bool on = (k<2);
      if(!on) sp=add(sp,R(1,7));
      V3 v=lin(R(1),T1,s,e1); v=lin(R(1),v,sp,e2);
      Q qv=dot(v,v), D=add(R(1),qv);
      Q x0=dv(sub(R(1),qv),D); V3 x=lin(dv(R(2),D),v,R(0),v);
      if(!eq(add(mul(x0,x0),dot(x,x)),R(1))) {bad++; printf("detX fail\n");}
      // tr(X P1^-1) with P1 = -1/2 + n1
      Q t1=mul(R(2),add(mul(x0,R(-1,2)),dot(x,n1)));
      if(!eq(t1,R(1))) {bad++; printf("plane fail\n");}
      Q t=mul(R(2),add(mul(x0,p0),dot(x,p)));
      bool inc=eq(t,R(1));
      if(inc!=on) {bad++; printf("incidence mismatch on=%d\n",(int)on);}
      tests++;
    }
  }
  printf("tests=%d bad=%d\n",tests,bad);
  return bad?1:0;
}
