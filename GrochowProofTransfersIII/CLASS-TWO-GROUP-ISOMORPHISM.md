# A faster isomorphism bound for groups of class two

## Theorem

Two finite groups of nilpotency class at most two and order $N$, given by Cayley tables, can be tested for isomorphism in time
$$
N^{O((\log N)^{19/20}(1+\log\log N)^{1/10})}.
$$
The bound is uniform in the primes dividing $N$ and covers $2$-groups of arbitrary exponent. The trivial group is decided directly. The result improves the power $25/26$ in Sun’s Theorem 1.1 and Corollary 1.2. [Xiaorui Sun, *Faster Isomorphism for Groups of Class 2*, arXiv:2611.05920v1](https://arxiv.org/html/2611.05920v1)

The proof uses Sun's group restriction, tuple isometry and automorphism algorithms. Its new step is the simultaneous tuning of the tuple cutoff, the ring length and the group restriction parameters. The cutoff choice follows an idea in the pinned Davis–Astra rectangle-partition proof. That proof chooses its active side range from the actual aspect ratio, controls integer rounding and takes the better of two envelopes to obtain a uniform bound. Here the active block range depends jointly on matrix dimension and ring length, with the quadratic state-count bound covering the saturated regime. [Source proof, “Upper bound” and “Two strip reservations”](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/rectangle-partition-asymptotics/PROOF.md)

## 1. The ordered tuple subroutines with a variable cutoff

Let $p$ be a prime, $R=\mathbb Z/p^\tau\mathbb Z$ with $\tau\ge1$, and let the ordered alternating tuples have matrices of side $D\ge1$ and length $m$. Empty matrices require a trivial check. Write $L=1+\lceil\log_2(2\tau D)\rceil$. Define
$$
 F(D,\tau)=\tau D+\min\{D^2,\,D^{7/4}(\tau L)^{1/4}\}.
$$
Isometry, including an isometry matrix in the positive case, takes time $p^{O(F(D,\tau))}\operatorname{poly}(p,\tau,D,m)$. Automorphism generators can be computed in time $p^{O(F(D,\tau)+\tau D^{3/2})}\operatorname{poly}(p,\tau,D,m)$.

### Isometry

Sun's algorithm accepts an input threshold $0<\Delta<1$. Set $r=D^\Delta$ and implement the two comparisons using integer cutoffs $r$ and $\lfloor D/r\rfloor$. For $2\le r<D$, Lemma A.32 bounds its running-time exponent by a constant times
$$
  D^2/r+\tau Dr+\min\{D^2,\tau Dr^3 L\}.
  \tag{1}
$$
The constants are absolute for integer $r$. The preliminary block enumeration and the frequent-block calls in Theorem A.16 cost $p^{O(\tau Dr+D\log D)}$ times polynomial factors. Each infrequent type has multiplicity at most $\lfloor D/r\rfloor$. Theorem A.19 costs $p^{O(D^2/r)}$ times polynomial factors on such tuples, with the ring length absent from its exponential term. The sum of the squared sizes of the frequent blocks is $O(Dr)$. For their corrections to the infrequent block, the representative types have total dimension $O(r)$, so the two state-count bounds in Lemma A.31 give the minimum in (1). The $D\log D$ term is absorbed for the cutoff used below. Lemma A.30 gives correctness and returns a witness by backtracking. The same preprocessing for common free zero summands used in Appendix A applies before this algorithm. [Sun, Appendix A, especially Theorems A.16 and A.19 and Lemmas A.30–A.32](https://arxiv.org/html/2611.05920v1#A1)

For $D\ge3$, choose
$$
  r=\max\{2,\lfloor(D/(\tau L))^{1/4}\rfloor\}.
$$
This integer can be found by testing fourth powers and lies below $D$. If $x=(D/(\tau L))^{1/4}\ge1$, then $x/2\le r\le2x$. Thus $D^2/r\le2D^{7/4}(\tau L)^{1/4}$ and $\tau D r^3 L\le8D^{7/4}(\tau L)^{1/4}$. The term $\tau Dr$ is at most $\tau Dr^3 L$, and $D\log D=O(D^2/r)$ because $r\le2D^{1/4}$. In this regime $D^{7/4}(\tau L)^{1/4}\le D^2$. If $x<1$, then $r=2$, and (1) is $O(D^2+\tau D)$ using its quadratic branch. This also absorbs $D\log D$. For $D\le2$, direct enumeration costs $p^{O(\tau)}\operatorname{poly}(m,\tau,\log p)$. These estimates give the claimed $F$. The expression $F(D,\tau)$ is nondecreasing in $D$ at fixed $\tau$.

### Automorphisms

In Sun's automorphism routine retain the cutoff $\Delta=1/2$. The preliminary enumeration for this cutoff has exponent $O(\tau D^{3/2})$ by the first step of the proof of Lemma A.32. Theorem A.19 handles the infrequent block in time $p^{O(D^{3/2})}\operatorname{poly}(p,\tau,D,m)$. Each frequent standard block has side $O(\sqrt D)$, so the column search in Lemma A.34 enumerates at most $p^{O(\tau D^{3/2})}$ candidates at each step. The expensive test on a candidate is one isometry-with-witness call on a complementary tuple, whose side is at most $D$. Replace that call by the tuned isometry routine just proved and use monotonicity of $F$. The remaining work of Lemmas A.33–A.34 is polynomial in the enumerated sets and $p^\tau$, and the algorithm applies at most $D$ block steps. The resulting generators have the same correctness guarantee as in Theorem A.2. Their count is bounded by the running time needed to output them. [Sun, Lemmas A.33–A.34 and proof of Theorem A.2](https://arxiv.org/html/2611.05920v1#A1.SS6)

## 2. Substitution into the group restriction algorithm

Suppose $N=p^n$, with $n\ge1$. Sun's Lemma 4.16 permits positive integer parameters $\delta,\tau$ with $\tau\ge\delta+2$. It constructs the group restriction tests in time and number bounded by
$$
 p^{O(n^{17/9}(\log p)^{8/9}+nZ)},\qquad
 Z=n/\delta+n\delta/\tau+\delta^3 n^{4/9}(\log p)^2.
 \tag{2}
$$
A restriction uses $\zeta=O(Z)$ central generators in its orbit computation. For the class-two restriction test, the doubled ordered alternating tuples in Section 5.4 have side $D=O(n\delta^2)$ and length polynomial in $n,\tau$. Steps 5 and 6 of the extended-vector matching algorithm require one isometry witness and one automorphism generating set, respectively. Substitute both routines from Section 1. Isometry witnesses and generators satisfy the original interfaces, so the normalization in Lemma 5.24 and its correctness proof apply unchanged. [Sun, Lemma 4.16 and §5.4](https://arxiv.org/html/2611.05920v1#S5.SS4)

Set $D_* = \lceil Cn\delta^2\rceil$ for a fixed sufficiently large absolute $C$, and use $F(D,\tau)\le F(D_*,\tau)$. The final orbit stage in the proof of Theorem 5.1 has at most $p^{O(n\zeta)}$ states. Each state transition and the preprocessing of generators cost polynomial time per generator and per state in the same input parameters. It therefore adds $O(n\zeta)$ to the exponent plus a constant multiple of the new generator-list exponent, which is already charged. Keep the other explicitly displayed term $\tau n^{3/2}\delta^7(1+\log(\tau n))$ in Sun's bound for the group restriction step. The exponent for that step is at most a constant times
$$
 F(D_*,\tau)+\tau D_*^{3/2}+
 \tau n^{3/2}\delta^7(1+\log(\tau n))+n\zeta .
 \tag{3}
$$
Polynomial work in the size of the Cayley table adds $O(n)$ to the exponent in base $p$. Multiplying the number of restrictions by the time for each test adds the exponents in (2) and (3). The restriction reduction and final orbit computation decide the original isomorphism instance. [Sun, proof of Theorem 5.1 in §5.5](https://arxiv.org/html/2611.05920v1#S5.SS5)

## 3. Uniform parameter choice

Let $B=1+\lfloor\log_2(n+1)\rfloor$. For all sufficiently large $n$, choose the largest integer $\delta\ge1$ with $\delta^{20}B^2\le n$, and put $\tau=\max\{\delta^2,\delta+2\}$. Bounded $n$ may use generator enumeration in polynomial time. For the chosen parameters,
$$
 \delta\asymp n^{1/20}B^{-1/10},\qquad
 \delta^2\le \tau\le3\delta^2,\qquad
 L_*:=1+\lceil\log_2(2\tau D_*)\rceil=O(B).
$$
The cutoff for $\delta$ can be computed by integer power comparisons. Here $\tau L_*\le D_*$ for all sufficiently large $n$, since $L_*=O(B)$ and $D_*\ge C n\delta^2$. It follows that all three cost terms in (3) other than $n\zeta$ are $O(n^2/\delta)$, as follows:
$$
\begin{aligned}
F(D_*,\tau)&=O(n^{7/4}\delta^4 B^{1/4}+n\delta^4),\
\tau D_*^{3/2}&=O(n^{3/2}\delta^5),\
\tau n^{3/2}\delta^7(1+\log(\tau n))&=O(n^{3/2}\delta^9 B).
\end{aligned}
$$
For the first line, $\delta^5 B^{1/4}\le n^{1/4}$ follows from $\delta^{20}B^2\le n$ and $B\ge1$. The second follows from $\delta^6\le n^{1/2}$, and the third from $\delta^{10}B\le n^{1/2}$. This proves the asserted bounds after division by $n^2/\delta$.

When $\log_2 p\le n^{1/10}$, the first two terms in $Z$ are $O(n^{19/20}B^{1/10})$, and the last satisfies
$$
 \delta^3 n^{4/9}(\log p)^2=O(n^{3/20+4/9+1/5})=O(n^{143/180}).
$$
Write $Q=\log_2 N=n\log_2 p$. After conversion from base $p$ to base $N$, the labeling term $n^{17/9}(\log p)^{8/9}$ becomes $O(Q^{8/9})$, while $n^2/\delta$ and $nZ$ become $O(n^{19/20}B^{1/10})$. This is $O(Q^{19/20}(1+\log Q)^{1/10})$.

When $\log_2 p>n^{1/10}$, find a generating list of at most $n$ elements from the first Cayley table by repeatedly adjoining an element outside the subgroup generated so far. Each adjunction multiplies the subgroup order by at least $p$. Enumerate the images of this list in the other group. Words for all group elements can be found by traversal with the listed generators, and a candidate map can be evaluated on these words and tested for bijectivity and preservation of the multiplication table in polynomial time. The enumeration costs $N^{n+O(1)}$, and $n<Q^{10/11}$. This fits the required bound.

Finally, a finite group of nilpotency class at most two is the direct product of its characteristic Sylow subgroups. Given a Cayley table, extract each Sylow subgroup by computing element orders and selecting the elements of prime-power order for that prime, including the identity. The preprocessing, including factoring $N$ by trial division, is polynomial in $N$. Apply the prime-power algorithm to corresponding subgroups and accept precisely when every comparison accepts. The number of primes is at most $\log_2 N$, which gives the stated bound.

## Verification and scope

This is a mathematical derivation from the stated results of Sun's preprint, with the particular new substitution audited at the interfaces above. The [companion Lean file](RestrictionCostBounds.lean) checks the three integer power comparisons used in Section 3. The full group and tuple algorithms are justified by the paper's cited results and the written composition. The earlier $N^{O((\log N)^{8/9})}$ algorithm for the odd-order subclass remains the stronger bound there. The improved exponent applies without an exponent bound on the input $2$-groups. Historical priority remains unverified. [Grochow, Qiao, Stange and Sun, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials V*, arXiv:2611.00735](https://arxiv.org/abs/2611.00735)
