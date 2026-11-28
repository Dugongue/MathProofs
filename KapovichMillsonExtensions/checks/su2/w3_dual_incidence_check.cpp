// W3: exact check over Q[eps]/(eps^2) of W4's point/line/incidence relators.
// Quaternions over dual rationals; M2 realisation not needed: we check quaternion identities.
#include <cstdio>
#include <cstdlib>
#include <numeric>
typedef long long ll;
struct Q { ll n, d; };
static ll g(ll a, ll b){ a = a<0?-a:a; b = b<0?-b:b; while(b){ ll t=a%b; a=b; b=t;} return a?a:1; }
static Q mk(ll n, ll d=1){ if(d<0){n=-n;d=-d;} ll k=g(n,d); return {n/k,d/k}; }
static Q operator+(Q a,Q b){ return mk(a.n*b.d+b.n*a.d,a.d*b.d); }
static Q operator-(Q a,Q b){ return mk(a.n*b.d-b.n*a.d,a.d*b.d); }
static Q operator*(Q a,Q b){ return mk(a.n*b.n,a.d*b.d); }
static Q operator/(Q a,Q b){ return mk(a.n*b.d,a.d*b.n); }
static bool eq(Q a,Q b){ return a.n==b.n && a.d==b.d; }
struct D { Q a, b; }; // a + b eps
static D dm(Q a, Q b=mk(0)){ return {a,b}; }
static D operator+(D x,D y){ return {x.a+y.a,x.b+y.b}; }
static D operator-(D x,D y){ return {x.a-y.a,x.b-y.b}; }
static D operator*(D x,D y){ return {x.a*y.a, x.a*y.b+x.b*y.a}; }
static D inv(D x){ Q ia = mk(1)/x.a; return {ia, mk(0)-x.b*ia*ia}; }
static bool deq(D x,D y){ return eq(x.a,y.a)&&eq(x.b,y.b); }
struct H { D w,x,y,z; };
static H operator*(H p,H q){
  return { p.w*q.w - p.x*q.x - p.y*q.y - p.z*q.z,
           p.w*q.x + p.x*q.w + p.y*q.z - p.z*q.y,
           p.w*q.y - p.x*q.z + p.y*q.w + p.z*q.x,
           p.w*q.z + p.x*q.y - p.y*q.x + p.z*q.w };
}
static H conj(H p){ D z=dm(mk(0)); return {p.w, z-p.x, z-p.y, z-p.z}; }
static D nrm(H p){ return p.w*p.w+p.x*p.x+p.y*p.y+p.z*p.z; }
static bool heq(H p,H q){ return deq(p.w,q.w)&&deq(p.x,q.x)&&deq(p.y,q.y)&&deq(p.z,q.z); }
static void pr(const char*s,H p){ printf("%s: w=%lld/%lld+%lld/%lld e ...\n",s,p.w.a.n,p.w.a.d,p.w.b.n,p.w.b.d); }
// Cayley: X = ((1-q)+2v)/(1+q)
static H cay(D v1,D v2,D v3){
  D q = v1*v1+v2*v2+v3*v3; D one=dm(mk(1)); D den = inv(one+q);
  D two=dm(mk(2));
  return { (one-q)*den, two*v1*den, two*v2*den, two*v3*den };
}
int main(){
  D z0=dm(mk(0));
  // P1 = (-1+i+j+k)/2
  H P1 = { dm(mk(-1,2)), dm(mk(1,2)), dm(mk(1,2)), dm(mk(1,2)) };
  H minus1 = { dm(mk(-1)), z0,z0,z0 };
  H one = { dm(mk(1)), z0,z0,z0 };
  int bad=0;
  // v = v0 + eps v1, v0=(0,0,1), v1=(1,-1,0); p = p0 + eps p1, p0=(-1/10,-7/10,1/2), p1=(-3,0,-3/5)
  for(int neg=0; neg<2; ++neg){
    D v1={mk(0),mk(1)}, v2={mk(0),mk(-1)}, v3={mk(1), neg? mk(1):mk(0)}; // neg: v1 gets extra eps*e3 (breaks Pi and incidence)
    H X = cay(v1,v2,v3);
    D p1={mk(-1,10),mk(-3)}, p2={mk(-7,10),mk(0)}, p3={mk(1,2),mk(-3,5)};
    H P = { dm(mk(-1,2)), p1,p2,p3 };
    bool detX = deq(nrm(X),dm(mk(1)));
    bool detP = deq(nrm(P),dm(mk(1)));
    bool P3 = heq(P*P*P, one);
    H Y = X*conj(P1); bool pt = heq(Y*Y*Y, minus1);
    H Z = X*conj(P);  bool inc = heq(Z*Z*Z, minus1);
    printf("case %s: det X=1:%d det P=1:%d P^3=1:%d (XP1^-1)^3=-1:%d (XP^-1)^3=-1:%d  trZ/2=%lld/%lld+%lld/%lld eps\n",
      neg?"perturbed":"incident", detX,detP,P3,pt,inc, Z.w.a.n,Z.w.a.d,Z.w.b.n,Z.w.b.d);
    if(!neg && !(detX&&detP&&P3&&pt&&inc)) bad++;
    if(neg && (pt||inc)) bad++;
  }
  // line lemma (orthonormal-free form): residual of P1 on the line {v in Pi: v.p = 1/2}
  // check: for p0 above, gamma=(1-a)/2 with a = p.n1/q(n1); and kappa formula with A,B in an orthonormal basis is checked by W4.
  printf(bad? "FAIL\n":"ALL OK\n");
  return bad;
}
