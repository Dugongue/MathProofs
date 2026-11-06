# Coefficients and root scales of general-position polynomials

## The questions

Section 4 of Bilal Ahmad Rather's preprint asks exactly which balanced complete multipartite graphs have unimodal or log-concave general-position polynomials. The two classifications below answer both questions for all parameters. Section 8 also raises the problem of bounding zeros. The root results below give the exact minimum modulus and determine the order of the logarithm of the maximum modulus. [Rather, arXiv:2603.06930v3](https://arxiv.org/html/2603.06930v3).

The coefficient proof uses the sequence decomposition strategy from the MathProofs proof of T-star unimodality. Here the summands come from two types of general-position sets. Bounding the mixed terms localizes every potential failure to a single index. [MathProofs T-star certificate](https://github.com/Dugongue/MathProofs/blob/fa15719245c37036228aec86a48637f651d95ec9/TStarUnimodality.lean).

## The two classifications

Write \(G=K_{r,\ldots,r}\) with \(t\ge2\) parts of size \(r\ge1\). Let \(a_j\) count the sets of \(j\) vertices in which no three distinct vertices lie on one shortest path.

1. The coefficient sequence is log-concave exactly when \(r\le t+1\) or \((t,r)=(2,4)\). When log-concavity fails, it fails at the single index \(t+1\).
2. The coefficient sequence fails to be unimodal exactly when \(r\ge2t+4\) and
   \[
   (t+1)r^t>t\binom rt(r-2t-1).
   \]
   For fixed \(t\), the exceptional values of \(r\) form a nonempty finite interval starting at \(2t+4\). For \(t=2,3,4\), these intervals are respectively \(\{8\}\), \([10,16]\), and \([12,43]\), with integer endpoints. For every \(t\ge5\), the last exceptional value is
   \[
   (t+1)(t-1)!+2t+\binom t2.
   \]

### Coefficient decomposition

Set \(A_j=\binom tj r^j\) and \(B_j=t\binom rj\), with out-of-range binomial coefficients zero. A general-position set either lies entirely in one part or meets each part in at most one vertex. Indeed, two vertices in one part and a third in a different part form a shortest path of length two. Each of the stated types avoids this pattern, the only possible kind of shortest-path triple in this graph. The two types are disjoint at sizes at least two, so
\[
a_0=1,\qquad a_1=tr,\qquad a_j=A_j+B_j\quad(j\ge2).
\]
Both summand sequences are log-concave by their successive binomial coefficient ratios. The full sequence is positive on its support from \(0\) through \(\max(t,r)\).

### Log-concavity away from the boundary

At index \(1\), use \(a_2=\binom{tr}{2}\) to obtain \(a_1^2\ge a_0a_2\). At index \(2\), \(a_1=A_1\). The normalized mixed term obeys
\[
\frac{A_1B_3}{A_2^2}\le\frac{2}{3(t-1)^2}.
\]
This follows from \(B_3\le tr^3/6\). For \(t\ge3\), the right-hand side is at most \(1/6\), whereas \((A_2^2-A_1A_3)/A_2^2\ge1/3\). For \(t=2\), the latter ratio is \(1\), exceeding the bound \(2/3\). In either case \(a_2^2\ge A_2^2\ge a_1a_3\).

For \(3\le j\le t-1\), let \(u=t-j\). The pure \(A\) terms have slack
\[
\frac{A_j^2-A_{j-1}A_{j+1}}{A_j^2}
=1-\frac{ju}{(j+1)(u+1)}\ge\frac1{j+1}.
\]
Using \(B_i\le tr^i/i!\) gives
\[
\frac{A_{j-1}B_{j+1}+B_{j-1}A_{j+1}}{A_j^2}
\le\frac{t}{\binom tj(j-1)!(j+1)}
\left(u+\frac{1}{u+1}\right)<\frac1{j+1}.
\]
For the strict inequality, \(\binom tj\ge t(u+1)/2\): at \(j=t-1\) this is equality, and otherwise \(\binom tj\ge\binom t2\) and \(u+1\le t-1\). Now \((j-1)!\ge2\) and \(u+1/(u+1)<u+1\). The pure \(B\) terms have nonnegative slack, and the mixed terms on the square side are nonnegative. This proves the required inequality.

At \(j=t\ge3\), the pure \(A\) slack is \(A_t^2\), since \(A_{t+1}=0\). The remaining mixed term satisfies
\[
\frac{A_{t-1}B_{t+1}}{A_t^2}\le \frac{t}{(t+1)(t-1)!}<1.
\]
For every \(j>t+1\), all three coefficients in the inequality come entirely from \(B\).

### The boundary at \(t+1\)

If \(r\le t+1\) then \(a_{t+2}=0\), and log-concavity holds. Otherwise \(B_{t+2}>0\). The inequality fails if and only if
\[
r^t>\frac{B_{t+1}^2}{B_{t+2}}-B_t
=t\binom rt\frac{r+1}{(t+1)(r-t-1)}.
\]
For \(t\ge3\), the right side divided by \(r^t\) is at most \((t+3)/((t+1)(t-1)!)<1\). This uses \(\binom rt\le r^t/t!\) and \((r+1)/(r-t-1)\le t+3\) for \(r\ge t+2\). For \(t=2\) and \(r\ge4\), failure reduces to \(2r^2-9r+1>0\), which holds exactly when \(r\ge5\).

### Unimodality

The log-concave prefix through index \(t+1\) is unimodal. If \(r\le2t+3\), the binomial tail starting at \(t+1\) is nonincreasing, so the whole sequence is unimodal.

Suppose \(r\ge2t+4\). Both summands increase weakly through index \(t\). For \(A\) this follows from \(A_j/A_{j-1}=r(t-j+1)/j\ge r/t>1\) for \(1\le j\le t\). For \(B\) it follows from its binomial ratios. At the initial indices \(a_0\le a_1\le a_2\) follows from \(tr\ge3\). After index \(t+1\) there is a strict rise to \(a_{t+2}\) followed by the rest of the unimodal binomial tail. Thus nonunimodality occurs precisely when \(a_t>a_{t+1}\). Substituting the formulas gives the stated inequality.

For fixed \(t\), the right side after division by \((t+1)r^t\) is a positive constant times
\[
(r-2t-1)\prod_{i=0}^{t-1}(1-i/r).
\]
It increases strictly to infinity for \(r\ge2t+4\). At \(r=2t+4\) the quotient is strictly less than \(3/((t+1)(t-1)!)\le1\), since the product is strictly less than one. This proves the interval claim.

For its exact upper endpoint, write \(C=(t+1)(t-1)!\), \(D=2t+1\), \(s=\sum_{i=1}^{t-1}i=\binom t2\), and \(p=\sum_{1\le i<j\le t-1}ij\). Failure is equivalent to \(F(r)<C\) for \(F(r)=(r-D)\prod_{i=1}^{t-1}(1-i/r)\). The first two inclusion-exclusion bounds for the product give
\[
r-D-s+\frac{sD}{r}
\le F(r)
\le r-D-s+\frac{sD+p}{r}
\qquad(r\ge2t+4).
\]
At \(r=C+D+s\) the lower bound is strictly greater than \(C\). At \(r=C+D+s-1\) the upper bound is strictly less than \(C\) if \(sD+p<r\). For \(t=5\) this compares \(145<164\). For \(t\ge6\), we have \(sD+p\le t^4/8+t^3+t^2/2<t^4/2\le C\). The last inequality holds at \(t=6\) and propagates since \(C\) grows by a factor \(t(t+2)/(t+1)\ge t\) while \(t^4\) grows by a factor \((1+1/t)^4<2\). For \(t=2,3,4\), direct substitution at the reported upper endpoint and its successor gives the stated intervals.

## Extremal moduli of zeros

For connected graphs on \(n\ge2\) vertices, the smallest attainable modulus of a general-position root is exactly
\[
\binom n2^{-1/2}.
\]
The minimizers are paths and the four-cycle. The largest attainable modulus over the same class is \(2^{\Theta(n)}\).

### Exact minimum

The graph with \(n=2\) has polynomial \((1+x)^2\). Suppose \(n\ge3\). General-position sets are closed under taking subsets. Counting extensions from \(j\)-sets to \((j+1)\)-sets gives \((j+1)a_{j+1}\le(n-j)a_j\). Since all vertex pairs are counted, \(a_2=\binom n2\). Set
\[
P(z)=\psi_G(z/\sqrt{a_2})=1+bz+z^2+\sum_{j\ge3}c_j z^j,
\qquad b=n/\sqrt{a_2}.
\]
Set \(c_2=1\) and extend the coefficients by zeros. The extension inequality gives
\[
c_{j+1}\le\frac{n-j}{(j+1)\sqrt{a_2}}c_j
\le\frac{3}{2(j+1)}c_j\quad(j\ge2).
\]
The latter bound holds since \((n-j)/\sqrt{a_2}\le\sqrt{2}<3/2\).

Consider \(z=R e^{i\theta}\) with \(0<R<1\). By conjugation it suffices to take \(0\le\theta\le\pi\). If \(0\le\theta\le\pi/2\), the real part of \(P(z)/z\) is positive. Indeed the real part from \(z^{-1}+b+z\) is at least \(b\), and the tail has modulus at most \(c_3/(1-3/8)\le4/5<b\).

If \(\pi/2\le\theta<\pi\), put \(x=-\cos\theta\), \(d_k=c_{k+1}R^k\) for \(k\ge2\), and \(S_k=\sin(k\theta)/\sin\theta\). The imaginary part of \(P(z)/z\), divided by \(\sin\theta\), is
\[
R-R^{-1}+\sum_{k\ge2}d_k S_k.
\]
Here \(S_2=-2x\), \(S_3=4x^2-1\), \(S_4=4x-8x^3\), and \(|S_k|\le k\) by the finite geometric sum for the sine ratio. In addition,
\[
d_3\le \tfrac38 d_2,\quad d_4\le \tfrac3{10}d_3\le\tfrac9{80}d_2,
\qquad
\sum_{k\ge5} k d_k\le \tfrac{105}{208}d_3\le\tfrac{13}{25}d_3.
\]
For the tail bound the first term \(5d_5\) is at most \(3d_3/8\) and each successive term is at most \(9/35\) times the preceding one, by the coefficient inequality. The weighted sine sum is nonpositive in each of three ranges.

- If \(0\le x\le1/5\), discard \(d_2S_2\). Then \(S_3\le-21/25\) and \(S_4\le4/5\), so the remaining sum is at most \((-21/25+(4/5)(3/10)+13/25)d_3\le0\).
- If \(1/5\le x\le1/2\), use \(S_3\le0\) and \(S_4\le4x\). The sum is at most \((-31x/20+39/200)d_2\le0\).
- If \(1/2\le x\le1\), use \(S_3\le3x\) and \(S_4\le4x\). The sum is at most \((-17x/40+39/200)d_2\le0\).

Thus the imaginary part is strictly negative in this range.

For \(\theta=\pi\), the alternating tail after degree three is nonnegative, so \(P(-R)\ge1-bR+R^2-c_3R^3\ge1-bR+(1-c_3)R^2\). We have
\[
b+c_3\le b\left(1+\frac{n-2}{3n}\right)\le\frac{10\sqrt3}{9}<2.
\]
For the second inequality, \((2-s)/\sqrt{1-s}\) is increasing for \(0\le s\le1/3\), and here \(s=1/n\). The quadratic lower bound is positive on \([0,1]\). If its minimum is at \(1\), use \(2-b-c_3>0\). If its minimum is at its vertex \(v\in[0,1]\), the value is \(1-bv/2>0\). This excludes the last possible angle. Since \(P(0)=1\), the whole open unit disk is root-free.

If \(c_3>0\), the same argument excludes roots on \(|z|=1\). In the left open half of the upper semicircle, \(x>0\). The first range has the strictly negative term \(-2xd_2\) that was discarded, and in the other two ranges the displayed bounds are strict because \(d_2>0\). The right half and negative real axis already had strict bounds. Thus equality in the root bound requires \(a_3=0\). Conversely, if \(a_3=0\), there are no larger general-position sets by closure under subsets. The polynomial is then \(1+nx+\binom n2x^2\), whose conjugate roots for \(n\ge3\) have the stated modulus.

In a connected graph with \(a_3=0\), a triangle is impossible since its three vertices would be a general-position set. Three neighbors of any vertex would then have all three pairwise distances equal to two and would also be a general-position set. Consequently the maximum degree is at most two, leaving paths and triangle-free cycles. In a cycle on \(n\ge5\) vertices, choose three cyclically consecutive gaps as equal as possible, each strictly less than \(n/2\). Each shortest path between two chosen vertices avoids the third. Hence only the four-cycle can have \(a_3=0\) among triangle-free cycles. Every triple in a path or four-cycle does lie on a shortest path, proving the claimed list of minimizers.

### Exponential scale of the maximum

For an upper bound let \(M=\max_{j<d}a_j/a_d\le2^n\). At \(|z|>1+M\), summing the geometric series gives \(\sum_{j<d}a_j|z|^j<a_d|z|^d\), ruling out a root. To obtain an exponential root for every sufficiently large \(n\), choose \(t=\lfloor(n+1)/3\rfloor\) and make a complete multipartite graph with \(t\) parts. Use one part of size \(t+1\), \(t-2\) parts of size \(2\), and one part of size \(2+n-(3t-1)\). For \(t\ge4\) the first part is uniquely largest. By the same shortest-path argument as before, the degree is \(t+1\), the leading coefficient is \(1\), and \(a_t\ge(t+1)2^{t-1}\) from the choices of one vertex in each part. Vieta's formula gives a root of modulus at least \(a_t/(t+1)\ge2^{t-1}\). This proves the claimed exponential scale.

## Priority and scope

These are informal proofs. The priority search did not locate an earlier full coefficient classification or an earlier exact minimum-modulus bound for general-position polynomials. The modulus theorems address precise versions of the broader question in Section 8 about zeros. The real-rootedness classification was already obtained and formalized by TrureTuring, which proves that a finite nonempty connected graph has a real-rooted general-position polynomial exactly when it is complete. The known counterexamples to preservation of unimodality under the corona operation also have prior credit. [TrureTuring real-rootedness dossier](https://www.trureturing.org/research/rather-2026-general-position-real-rooted-complete/), [Rather, Sections 6–8](https://arxiv.org/html/2603.06930v3#S6).
