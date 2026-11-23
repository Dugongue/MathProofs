# Phase moments and collective failures of concavity

Let $\xi=(\xi_1,\ldots,\xi_n)$ take values in the unit torus with law $\mu$. For nonnegative real amplitudes $z$, write
$$
 M_{\mu,\ell}(z)=\mathbb E_\mu\left|\sum_i z_i\xi_i\right|^{2\ell},
 \qquad
 F_{\mu,m}(x)=M_{\mu,m}(x_1^{1/(2m)},\ldots,x_n^{1/(2m)}).
$$
Subscript $0$ denotes product Haar measure. A coordinate face indexed by $S\subseteq[n]$ sets every coordinate outside $S$ to zero. A face is a minimal failure if its response is nonconcave and all its proper coordinate faces are concave. The collection of these faces is an antichain.

The original construction gives exactly the $2m$-uniform antichains when all $(2m-1)$-marginals are fixed to product Haar. The results below give the following refinements.

- A prescribed antichain with face sizes from $3$ through $2m$ is realizable even when all lower even moments are fixed. The two-coordinate criterion depends exactly on the real pair correlation, so matching just the second moments already excludes the smaller failures.
- Lowering the observed marginal order by just one destroys every dimension-independent bound on the size of a minimal failure. An explicit two-parameter family has an exact collective concavity threshold on each face dimension.
- Arbitrary finite antichains can be realized after adjoining private coordinates, while preserving all the lower moments and all $(2m-2)$-marginals.
- Uniform interior stability and a weighted local comparison give explicit sufficient certificates. The sharp collective family has unbounded positive curvature near the boundary at arbitrarily small total variation distance from independence.

[Original field proposal and uniform theorem](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md)

## 1. Exact information carried by real-amplitude moments

For an integer charge $v$ let $\xi^v=\prod_i\xi_i^{v_i}$. A charge is balanced if $\sum_i v_i=0$. For a nonnegative integer vector $a\ne0$ put
$$
 B_\mu(a)=\sum_{\substack{|v_i|=a_i\ (\forall i)\\\sum_i v_i=0}}\mathbb E_\mu \xi^v ,
 \qquad q(a)=\frac12\sum_i a_i.
$$
An empty sum is zero. The group is real by pairing $v,-v$. For every $\ell$,
$$
 M_{\mu,\ell}(z)=M_{0,\ell}(z)+
 (\ell!)^2\sum_{\substack{a\ne0\\ q(a)\in\{1,\dots,\ell\}}}
 B_\mu(a)
 \sum_{\substack{\gamma\ge0\\|\gamma|=\ell-q(a)}}
 \frac{z^{a+2\gamma}}{\prod_i(a_i+\gamma_i)!\gamma_i!}.
$$
Indeed the two multi-indices in the usual moment expansion are the positive and negative parts of $v$, each plus the same $\gamma$. The denominator depends only on $a,\gamma$.

**Proposition 1.** Agreement of the moments of orders $2,\dots,2t$ with independence, for all real nonnegative amplitudes, is equivalent to $B_\mu(a)=0$ whenever $1\le q(a)\le t$. Under agreement for $t=m-1$,
$$
 F_{\mu,m}(x)=F_{0,m}(x)+\sum_{|a|=2m} c_a x^{a/(2m)},
 \qquad c_a=\frac{(m!)^2}{\prod_i a_i!}B_\mu(a).
$$
In particular the unresolved coefficients are precisely these groups, subject to the positivity constraints on a probability law.

The implication from the groups to moment agreement is the displayed expansion. Conversely induct on $\ell$, then compare polynomial coefficients of the remaining distinct monomials $z^a$ at order $2\ell$. The phase-resolved experiment, where the amplitudes themselves range over $\mathbb C^n$, separates individual charges by Fourier integration in the amplitude phases. It therefore distinguishes more than the real-amplitude experiment in general.

For any finite list of distinct admissible $a$ of positive mass $m$, choose one balanced representative $v_a$ per $a$. The density
$$
 \rho(\theta)=1+\sum_a t_a\cos(v_a\cdot\theta),\qquad \sum_a|t_a|<1
$$
has $B_\mu(a)=t_a$ on the listed coefficients and zero elsewhere. It preserves every coordinate Haar marginal whose coordinate set contains no selected charge support. This gives an explicit neighborhood of achievable signed coefficient vectors, with smooth strictly positive densities converging to product Haar as the coefficients are scaled to zero. The lower even moments also agree for complex amplitudes in these constructions, since all their nonzero charges have positive mass $m$.

## 2. Exact two-face exclusion and nonuniform small-face realization

**Theorem 2.** On a two-coordinate face $\{i,j\}$, $F_{\mu,m}$ is concave exactly when
$$
 \mathbb E_\mu \operatorname{Re}(\xi_i\overline{\xi_j})\ge0 .
$$
This holds for every phase law and every $m\ge1$. Thus agreement with the independent second moment already rules out two-coordinate failures. For $m\ge2$, every antichain $\mathcal A$ of sets with $3\le|A|\le2m$ is nevertheless the exact minimal failure collection for a smooth, strictly positive law arbitrarily close to product Haar, with all lower even moments fixed. The realization also preserves every prescribed product-Haar marginal on sets containing no member of $\mathcal A$.

For the exact two-face criterion, write $T=\operatorname{Re}(\xi_i\overline{\xi_j})$, set the second coordinate to one, and let $u=x_i^{1/(2m)}$. The restricted function is $f(u)=\mathbb E A^m$, $A=1+u^2+2uT$. Its second derivative in $x_i$ is nonpositive exactly when $(2m-1)f'(u)-uf''(u)\ge0$. For $m\ge2$, direct differentiation gives
$$
 (2m-1)f'-uf''
 =2m\left[
 2(m-1)u\,\mathbb E\bigl((1-T^2)A^{m-2}\bigr)
 +(2m-1)\mathbb E(TA^{m-1})\right].
$$
The first term is nonnegative. When $\mathbb ET\ge0$, the second is nonnegative because $A^{m-1}\ge0$ and $A^{m-1}$ is increasing in $T$. The monotone covariance identity follows by taking independent copies $T,T'$ and expanding $\mathbb E[(T-T')(A^{m-1}(T)-A^{m-1}(T'))]\ge0$. If $\mathbb ET<0$, the coefficient $2m\,\mathbb ET$ of the lowest positive power $x_i^{1/(2m)}$ is negative, giving positive second derivative near zero. The full restriction is the perspective of the one-variable slice by homogeneity. Continuity includes the boundary. For $m=1$ the face formula is directly $x_i+x_j+2\mathbb ET\sqrt{x_ix_j}$.

For realization, each $A$ with $3\le|A|\le2m$ supports a balanced charge of positive mass $m$ having an entry of magnitude one. Split $A$ into two nonempty groups, each of size at most $m$, one of size at least two. Give the latter group a prescribed unit entry and distribute the remaining mass $m-1$ positively over the rest. Distribute mass $m$ positively over the other group and give that group the opposite sign. In Proposition 1 take a negative Fourier coefficient for this charge and no other terms. In the sum over $\mathcal A$, a face containing no $A$ has response $F_0$. On the face $A$, every other antichain term vanishes. Set one unit-magnitude coordinate to $t$ and the other coordinates in $A$ to one. The negative term has a positive second derivative of order $t^{1/(2m)-2}$, while every nonconstant independent monomial has exponent at least $1/m$ in $t$. This gives precisely the claimed failures. The Fourier construction proves the observation and total variation statements.

If the lower-moment requirement is dropped, the same argument realizes all antichains with sizes from $2$ through $2m$. On a two-set use the negative charge $(1,-1)$ of positive mass one. Its order-$2m$ correction consists of negative terms, with smallest exponent $1/(2m)$ on either coordinate by allocating all repetitions to the other coordinate. Hence it gives the same boundary witness. On every remaining set retain the mass-$m$ construction. The observations supported on sets containing no member of the antichain remain product Haar.

If all $(2m-1)$-marginals are observed, a surviving $2m$-charge has unit magnitude in every coordinate of its support. The coefficients on each $2m$-face are then separately necessary and sufficient for concavity, by the same boundary argument. If all $2m$-marginals are observed, every group in the response is forced to its independent value. These facts recover the original exact arity $2m$.

## 3. A sharp collective threshold in every even order

Write $k=2m$ and now use $z_i=x_i^{1/k}$. For $\alpha,\beta\ge0$ consider
$$
 G(x)=F_{0,m}(x)+
 \alpha\sum_{|J|=k-1}\sum_{d\in J}z_d\prod_{j\in J}z_j
 -\beta\sum_{|K|=k}\prod_{i\in K}z_i.
 \tag{1}
$$
The correction can be realized by Proposition 1 after any sufficiently small common scaling of $\alpha,\beta$. The $(k-1)$-support exponent doubles one coordinate and is balanced by putting that doubled coordinate and $m-2$ unit coordinates on one side. The $k$-support exponent has all units and its signs split equally. The density therefore preserves every $(k-2)$-marginal and all the lower even moments.

**Theorem 3.** On a face of size $s<k$, (1) is concave. On a face of size $s\ge k$, it is concave exactly when
$$
 \beta\ \le\ \frac{(k-1)(k-2)}{s-k+1}\alpha .
 \tag{2}
$$
In consequence, for every $L$ with $k\le L\le n$, all $L$-sets can be exactly the minimal failure faces, with product-Haar $(k-2)$-marginals and all lower even moments. In particular a fixed moment order and the complete set of $(k-2)$-marginals put no uniform bound on the size of a minimal failure.

### Proof of (2)

For a monomial $x^w$ of total exponent one and a direction $h$, set $u_i=h_i/x_i$. Then
$$
 -D^2 x^w[h,h]=x^w\sum_{i<j}w_iw_j(u_i-u_j)^2.
 \tag{3}
$$
This follows by differentiating twice and using $\sum_i w_i=1$. All weights on the right are nonnegative.

Fix a $k$-set $K$ and abbreviate $Z=\prod_{i\in K}z_i$ and $Q_K=\sum_{i<j\in K}(u_i-u_j)^2$. For distinct doubled and omitted coordinates $d,o$, let $Q_{d,o}$ be the same weighted pair sum on $K\setminus\{o\}$, with integer weights two at $d$ and one at the other coordinates. The curvature of that monomial is $k^{-2}Z(z_d/z_o)Q_{d,o}$. Let $R=K\setminus\{d,o\}$, $\bar u_R$ its average, and $V_R=\sum_{i\in R}(u_i-\bar u_R)^2$. Writing $r=k-2$, expand
$$
 Q_{d,o}=2r(u_d-\bar u_R)^2+kV_R .
$$
Pairing the two reciprocal terms for $d,o$, AM–GM followed by Cauchy–Schwarz gives
$$
 \frac{z_d}{z_o}Q_{d,o}+\frac{z_o}{z_d}Q_{o,d}
 \ge 2\sqrt{Q_{d,o}Q_{o,d}}
 \ge 4r(u_d-\bar u_R)(u_o-\bar u_R)+2kV_R.
$$
The difference between the leftmost and rightmost sides is explicitly
$$
 \frac{2r\bigl(z_d(u_d-\bar u_R)-z_o(u_o-\bar u_R)\bigr)^2+
       kV_R(z_d-z_o)^2}{z_dz_o}.
$$
Thus the comparison is a sum-of-squares identity after multiplication by the monomial denominators.
After summing over unordered $d,o$, the last expression is a symmetric translation-invariant quadratic form in $u$, and hence a scalar multiple of $Q_K$. To evaluate the scalar take one $u_i=1$ and all others zero. Pairs involving $i$ contribute zero to the last expression. Both $Q_{d,o}$ and $Q_{o,d}$ for all other pairs equal $k-1$, and Cauchy–Schwarz in the second step is equality there. Thus the scalar is $(k-1)(k-2)$. We have proved the pointwise curvature comparison
$$
 \sum_{\substack{J\subset K\\|J|=k-1}}\sum_{d\in J}
       -D^2\!\left(z_d\prod_{j\in J}z_j\right)[h,h]
 \ \ge (k-1)(k-2)\left(-D^2\prod_{i\in K}z_i[h,h]\right).
 \tag{4}
$$
The constant is sharp by the same direction $u$ and letting $z_i$ tend to zero with the other $z$'s fixed at one.

Sum (4) over all $k$-sets inside the face. Every positive monomial is counted $s-k+1$ times. This proves sufficiency in (2), even for the correction alone. For necessity set one coordinate $x_i=t$ and all other face coordinates to one. Only terms where $i$ occurs to power $1/k$ can contribute at the smallest positive power. Their net coefficient is
$$
 -\Delta_s=\alpha(k-2)\binom{s-1}{k-2}-\beta\binom{s-1}{k-1}.
$$
All other nonconstant terms have exponent at least $2/k$. Consequently
$$
 G''(t)=\frac{k-1}{k^2}\Delta_s t^{1/k-2}+O(t^{2/k-2}).
$$
If (2) fails, $\Delta_s>0$, so the response is nonconcave. This also gives a quantitative Jensen violation on the segment from $0$ to $t$ in the varying coordinate. For fixed $0<\lambda<1$, the Jensen difference is
$$
 G(\lambda t)-(1-\lambda)G(0)-\lambda G(t)
 =-\Delta_s(\lambda^{1/k}-\lambda)t^{1/k}+O(t^{2/k}).
$$
Concavity on an open face extends to its closed face by continuity. Choose $\beta/\alpha$ strictly above the threshold for $s=L$ and at or below the threshold for $s=L-1$ when $L>k$. When $L=k$, only the strict inequality is required. This proves the realization.

The gap between observing marginals on $k-1$ coordinates and observing marginals on $k-2$ coordinates is thus a sharp transition in the dimensions of minimal failure faces. On the smaller observation family even concavity on *every* proper coordinate face can coexist with failure on the full orthant.

## 4. Weighted certificates and arbitrary families with private coordinates

The curvature comparison (4) gives a weighted form. Give each $(k-1)$-set $J$ a nonnegative coefficient $\alpha_J$ common to its doubled monomials, and each $k$-set $K$ a negative monomial with magnitude $\beta_K\ge0$. On a face $S$, a sufficient condition for concavity of this correction is
$$
 \sum_{\substack{K\subseteq S\\K\supset J,\ |K|=k}}\beta_K
 \ \le (k-1)(k-2)\alpha_J
 \qquad(J\subseteq S,\ |J|=k-1).
$$
To prove it, allocate to each $K$ the coefficient $\beta_K/((k-1)(k-2))$ from each of its doubled monomials in (4). The prescribed budgets let one make all allocations and leave nonnegative unused curvature. The symmetric case proves sharpness of the universal factor in this sufficient criterion. Conversely, for every $i\in S$, any concave response of this form requires that
$$
 \sum_{\substack{J\subseteq S\\i\in J}}\alpha_J
       \left(\prod_{j\in J\setminus\{i\}}z_j\right)
       \sum_{d\in J\setminus\{i\}}z_d
 \ -\sum_{\substack{K\subseteq S\\i\in K}}\beta_K
       \prod_{j\in K\setminus\{i\}}z_j
 \ \ge0
$$
for all positive $z$ on the other coordinates. This is the coefficient of $x_i^{1/k}$. A negative value forces a positive second derivative as $x_i$ tends to zero. The load certificate and this boundary test agree exactly in the symmetric family.

**Corollary 4.** Let $\mathcal A$ be any finite nonempty antichain of nonempty coordinate sets. For each $A\in\mathcal A$ add private coordinates, disjoint from all the old coordinates and each other's additions, to form $\widetilde A$ of size at least $k-1$. At least one private coordinate is required per $A$. The resulting family $\{\widetilde A:A\in\mathcal A\}$ is the exact minimal concavity failure family of a smooth positive phase law preserving all $(k-2)$-marginals and all lower even moments. For sets already of size at least $k-2$, one private coordinate per set is enough.

On each augmented set of size at least $k$ use its own sharp collective correction with threshold exactly that size. On an augmented set of size $k-1$ use the single negative charge from Theorem 2, with a private coordinate of magnitude one. Add these corrections and scale the entire finite sum to give a positive Fourier density. Every face containing no augmented set sees a concave restriction of each correction separately. On the face of one augmented set, vary its private coordinate. The other corrections are constant in that coordinate, and the independent baseline has its first nonconstant exponent at least $2/k$. The chosen correction has a negative $x_i^{1/k}$ coefficient on this slice. This proves precisely the asserted failures. Coincident charges can be combined before choosing the scale.

For an existing antichain on the same ground set, no new coordinates are needed if each member $A$ of size at least $k$ has a witness coordinate $i_A$ such that every other member containing $i_A$ intersects $A$ in at most $k-2$ coordinates, and the corresponding condition holds for any $k-1$ member. Indeed every other correction is then constant along the chosen line on the face $A$. This includes hypergraphs whose pairwise intersections have size at most $k-2$.

## 5. Quantitative interior stability and open directions

Write $F_\mu-F_0=\sum_w b_w x^w$ in finitely many grouped monomials of total exponent one, without any lower-moment assumption. Put $B=\sum_w |b_w|$. On $[\eta,1]^n$, $0<\eta<1$, equation (3) gives
$$
 -D^2F_\mu(x)[h,h]\ \ge
 \left((m-1)\eta-\frac{B}{4}\right)\sum_{i<j}
    (h_i/x_i-h_j/x_j)^2.
$$
Indeed for each pair $i,j$, the independent monomial indexed by the multiplicities $m-1,1$ contributes at least $(m-1)\eta$ to that pair's coefficient. The total absolute contribution from the correction is at most $B/4$, since $w_iw_j\le1/4$ and $x^w\le1$. Moreover $B\le2n^{2m}\|\mu-\mu_0\|_{\rm TV}$ by summing the multinomial expansion and bounding each moment difference by twice total variation. Thus an explicit interior radius guarantees concavity, with strict curvature in nonradial directions below that radius. Theorem 3 shows why the radius cannot extend uniformly to coordinate boundary points.

Two questions suggested by the proofs are whether the one-coordinate boundary tests in Section 4 ever miss a collective failure for the weighted two-layer family, and which antichains on the unchanged ground set can be realized under fixed observation order without a private-coordinate hypothesis. A further quantitative problem is to find the optimal interior stability radius for a prescribed compatible marginal trace rather than using the uniform multinomial bound above.

These are written results about the specified real-orthant phase response. Exact integer arithmetic checked 606 cases of the symmetric curvature identity for even sizes 4 through 14. Finite independence and hypergraph-indexed marginals have prior literature, while signomial nonnegativity provides analogous AM–GM certificate methods. The distinctive calculation here is the sharp curvature inequality (4), which compares Hessian quadratic forms and produces a first failure of arbitrarily large support one marginal layer below the original realization theorem. Priority beyond the cited constructions remains provisional. [H-wise independence](https://doi.org/10.1145/2422436.2422495) · [Chandrasekaran–Shah, relative entropy and signomials](https://arxiv.org/abs/1409.7640) · [Jenkins–Tkocz, complex Hanner inequalities](https://arxiv.org/abs/2207.09122)
