# Finite extendibility and hidden phase moments

Suppose each set of $2m-1$ coordinates of a random vector on the unit circle has independent Haar law. Requiring its law to come from a larger exchangeable vector limits the hidden phase-moment coefficients even though no new coordinate marginal is observed. At fourth order the most negative coefficient has sharp asymptotic size $N^{-2}$ for an extension to $N$ variables, while a positive coefficient can be of order $N^{-1}$. Exact higher-moment responses can still conceal singular dependence.

## 1. The finite-extension observation

Let $\mathcal E_{m,N}$ be the exchangeable laws of $Z=(Z_1,\ldots,Z_N)\in\mathbb T^N$ whose $(2m-1)$-coordinate marginals are product Haar. An $n$-coordinate law is $N$-extendible in this class if it is the $n$-coordinate marginal of a member of $\mathcal E_{m,N}$. This is an additional constraint on the compatible laws. It does not supply the values of observations on the new coordinates.

All balanced, fully distinct moments are the same real number
$$
 a_m(Z)=\mathbb E[Z_1\cdots Z_m\overline Z_{m+1}\cdots\overline Z_{2m}].
$$
Reality follows by exchanging the two groups of indices. In the phase response
$$
 \mathbb E\left|\sum_{i=1}^n x_i^{1/(2m)}Z_i\right|^{2m},
$$
the coefficient of each full-support term indexed by a $2m$-set is $(2m)!a_m(Z)$, since there are $\binom{2m}{m}$ ways to split that set between the two sets of $m$ positions and $(m!)^2$ orderings for each split. Thus the hidden failure family in this symmetric setting is either empty or all $2m$-sets. What remains to determine is the magnitude available under extension. [Original phase-moment theorem](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md)

Write $(N)_j=N(N-1)\cdots(N-j+1)$. Let $S_Z=\sum_i Z_i$, $Y=|S_Z|^2/N$, and let $\nu_N$ be the distribution of $Y$ under the independent Haar law. Expanding the ordered products and using the marginals gives
$$
 \mathbb E Y^j=\int y^j\,d\nu_N(y)\quad(0\le j<m),\qquad
 \mathbb E Y^m-\int y^m\,d\nu_N(y)=\frac{(N)_{2m}}{N^m}a_m(Z).
 \tag{1}
$$
For the last equality, the only terms that can differ from the independent moment have all $2m$ positions occupied by distinct indices. This expansion suffices for the following bounds.

## 2. Sharp fourth-order bounds

**Theorem 1.** For $Z\in\mathcal E_{2,N}$, with $N\ge4$,
$$
  -\frac1{(N-2)(N-3)}\le a_2(Z)\le
  \frac1{2(N-3)}.
 \tag{2}
$$
If $a_N^-$ and $a_N^+$ are the minimum and maximum over this class, then
$$
     \lim_{N\to\infty}N^2 a_N^-=-1,
       \qquad a_N^+=\Theta(N^{-1}).
 \tag{3}
$$
Equality on the left is impossible at $N=4,5$. Equality on the right is impossible for continuous Haar marginals, and it holds in an auxiliary four-phase model at powers of two. The asymptotic exhaustions in (3) can be obtained with smooth strictly positive densities.

*Proof of (2).* The independent first two moments of $Y$ are $1$ and $2-1/N$. The second formula follows by counting $N$ terms with one index repeated four times and $2N(N-1)$ terms with two identical unordered pairs of indices. For the lower bound, Jensen gives $\mathbb EY^2\ge1$. For the upper bound, put $M_j=N^{-1}\sum_i Z_i^j$ and $t=|M_1|$. Rotate an outcome with $t>0$ so that $M_1=t$. Jensen on the squared real parts of the phases gives $\operatorname{Re}M_2\ge2t^2-1$ in this frame. It follows that $\operatorname{Re}(M_1^2\overline M_2)\ge2t^4-t^2$, also for $t=0$. Three-wise Haar gives $\mathbb E(M_1^2\overline M_2)=1/N^2$ by retaining only all-equal indices, and $\mathbb Et^2=1/N$. Therefore $\mathbb EY^2=N^2\mathbb Et^4\le(N+1)/2$. Substituting the two bounds into (1) gives (2). Equality on the right requires all real parts in the rotated frame to agree whenever $t>0$. There would then be at most two distinct phases on these outcomes. Product Haar pair marginals imply that all phases are distinct almost surely, while $\mathbb Et^2=1/N$ implies positive probability of $t>0$. This precludes equality. Compactness of probability measures on $\mathbb T^N$, closedness of the marginal and permutation constraints, and continuity of $a_2$ give the extrema. Equality at the lower endpoint requires $|S_Z|=\sqrt N$ almost surely. When $N=4,5$, the first three coordinates have positive probability to have sum of magnitude less than $\sqrt N-(N-3)$, by taking neighborhoods of three evenly spaced phases. Even making the remaining coordinates perfectly aligned cannot reach $\sqrt N$ on this event. $\square$

*Construction for the negative endpoint.* Let $p$ be an odd prime, let $d\ge2$ be even, and put $F=\mathbb F_{p^d}$, $M=p^d$. Denote the trace to $\mathbb F_p$ by $\operatorname{Tr}$, and fix a nonsquare $c\in F^\times$. Choose independent uniform variables
$$
 b\in\mathbb F_p,\qquad \alpha\in F,\qquad
 \beta\in\{v\in F: \operatorname{Tr}(cv)=1\}.
$$
For $x\in F$, put $W_x=\exp(2\pi i(\operatorname{Tr}(\beta x^2+\alpha x)+b)/p)$.

These discrete phases are three-wise independent and uniform over the $p$-th roots of unity. To check this, a charge vector $(\lambda_i)_{i=1}^3$ in $\mathbb F_p^3$ on distinct indices $x_i$ gives a zero Fourier moment unless
$$
 \sum_i\lambda_i=0,qquad
 \sum_i\lambda_i x_i=0,qquad
 \sum_i\lambda_i x_i^2\in c\mathbb F_p.
 \tag{4}
$$
The last condition is the annihilator of the translation space of the affine trace hyperplane, for the nondegenerate trace pairing. A nonzero vector satisfying the first two conditions has all three entries nonzero. They imply $x_3=x_1+t(x_2-x_1)$ with $t\in\mathbb F_p\setminus\{0,1\}$. Then
$$
 \sum_i\lambda_i x_i^2=\lambda_3 t(t-1)(x_2-x_1)^2.
$$
This is a nonzero square, because every element of $\mathbb F_p^\times$ is a square in the even-degree extension. Every nonzero element of $c\mathbb F_p$ is a nonsquare, so (4) is impossible. The same check with zero charges covers fewer variables. Fourier inversion on the $p$-ary cube gives the asserted marginals.

Every draw has $\beta\ne0$ and $\big|\sum_x W_x\big|=\sqrt M$. For this Gauss-sum identity, put $\psi(v)=\exp(2\pi i\operatorname{Tr}(v)/p)$. On squaring the magnitude and setting the difference of the two index variables equal to $v$, the inner sum is $\sum_x\psi(2\beta vx)$. It vanishes unless $v=0$, in which case it is $M$. After an independent uniform permutation of the $M$ coordinates, the phases are exchangeable. The fourth moment calculation of (1) also applies to these phases, since in a lower-support term the nonzero coordinate charge has magnitude at most two and $p$ is odd. Thus they attain the lower endpoint of (2) in the discrete model. The individual ingredients are standard Fourier orthogonality and quadratic Gauss sums. The useful combination is the affine trace slice that keeps three-point independence and excludes the degenerate quadratic. [Wootters–Fields, finite-field phase constructions](https://doi.org/10.1016/0003-4916(89)90322-9)

To obtain the claimed Haar marginals, multiply each coordinate independently by $e^{iV}$ with $V$ uniform on $[-\pi/p,\pi/p]$. The rotated sectors partition the circle up to endpoints, so every three-coordinate marginal is product Haar. The balanced coefficient is multiplied by
$$
  \rho_p^4,\qquad \rho_p=\frac{\sin(\pi/p)}{\pi/p}.
$$
In particular a member of $\mathcal E_{2,M}$ has $a_2=-\rho_p^4/((M-2)(M-3))$. For each sufficiently large $N$, use $d=2$ and the least odd prime $p$ with $p^2\ge N$. The prime number theorem gives $p/\sqrt N\to1$, because every interval $[x,(1+\varepsilon)x]$ contains a prime for large $x$ and fixed $\varepsilon>0$. Restrict the resulting law to $N$ coordinates. Its coefficient is unchanged, $M/N\to1$, and $\rho_p\to1$. Together with (2) this proves the negative limit in (3). [An elementary proof of the prime number theorem](https://arxiv.org/abs/2002.03255)

*Construction for the positive scale.* Let $M=2^h\ge4$ and index phases by $\mathbb F_2^h$. For independent uniform $b\in\mathbb F_2$, $\alpha\in\mathbb F_2^h$, the signs $\sigma_x=(-1)^{b+\alpha\cdot x}$ are three-wise independent. Any three distinct augmented vectors $(1,x)$ are linearly independent, since a relation would have even support and no two are equal. The sign sum is $\pm M$ with probability $1/M$ and zero otherwise, by character orthogonality. Take an independent copy $\tau$ and put $W_x=(\sigma_x+i\tau_x)/\sqrt2$. The phases are three-wise independent and uniform on a rotated set of four equally spaced phases. The independent sign sums satisfy
$$
 \mathbb E\left|\sum_x W_x\right|^4
  =\frac14\left(2M^3+2M^2\right).
$$
Uniformly permute the coordinates. The fourth moment formula gives $a_2=1/[2(M-3)]$, attaining the upper endpoint in this discrete model. Independent sector jitter with sectors of angle $\pi/2$ gives product Haar three-marginals and multiplies the coefficient by $\rho_4^4=64/\pi^4$. Take the least power of two $M\ge N$ and restrict to $N$ coordinates. This proves the lower bound of the positive order assertion. It also gives $\liminf_N N a_N^+\ge16/\pi^4$ and $\limsup_N N a_N^+\ge32/\pi^4$, with $\limsup_N N a_N^+\le1/2$ by (2).

For either construction an independent small circular smoothing can be made smooth and strictly positive. For example, use a convex mixture of a smooth bump supported close to one and a small portion of Haar. This operation keeps product-Haar low marginals and permutational symmetry, and multiplies the balanced coefficient by $|\mathbb E\eta|^4\to1$, with $\eta$ the smoothing phase. This proves the final assertion. $\square$

In particular, no finite exchangeability length settles concavity in this trace. A negative law exists for every $N$, and every $4$-face then fails concavity, although the coefficients cannot stay a fixed negative distance from zero as the extension length grows.

## 3. A sharp scalar bound at all even response orders

**Theorem 2.** Let $m\ge2$, $N\ge2m$, $r=\lfloor m/2\rfloor$, and $\delta=m-2r\in\{0,1\}$. Let $P_N$ be the unique monic degree-$r$ polynomial orthogonal to degrees less than $r$ for the measure $y^\delta\,d\nu_N(y)$. Put $B_{m,N}=\int y^\delta P_N(y)^2\,d\nu_N(y)$. For every $Z\in\mathcal E_{m,N}$,
$$
 a_m(Z)\ge -\frac{N^m}{(N)_{2m}}\,B_{m,N},
 \qquad
 \lim_{N\to\infty} B_{m,N}
 =\lfloor m/2\rfloor!\,\lceil m/2\rceil!.
 \tag{5}
$$
The bound is exact if only the scalar observations $\mathbb E Y^j$ for $0\le j<m$ and the constraint $0\le Y\le N$ are used.

*Proof.* The support of $\nu_N$ is $[0,N]$. The map from $\mathbb T^N$ to $Y$ is continuous, takes the endpoints by alignment or equally spaced phases, and has full-support input law. Its image is connected. Thus the inner product defining $P_N$ is positive definite. The monic polynomial $y^\delta P_N(y)^2$ has leading term $y^m$, and its lower-degree integrals for $Y$ are fixed by (1). It is nonnegative on $[0,N]$. Subtract its integral under $\nu_N$ from its expectation to get (5).

For the exact scalar assertion, $P_N$ has $r$ distinct roots in $(0,N)$. Otherwise multiply it by the product of its sign-changing roots there, which would have degree less than $r$; the product would have constant sign, contradicting orthogonality. Use these roots as quadrature nodes, including $0$ also when $\delta=1$. Define the weights by integrating each node's Lagrange polynomial against $\nu_N$. To prove exactness through degree $m-1$, divide a test polynomial by $y^\delta P_N(y)$. The remainder interpolates at the nodes, and the quotient has degree at most $r-1$, so the integral of the divided-off term is zero. The weights are positive because exactness applies to the square of each Lagrange polynomial: its degree is at most $2(r+\delta-1)\le m-1$, and its integral is positive. The weights sum to one. The resulting probability measure is supported where $y^\delta P_N(y)^2$ vanishes, which attains equality.

For each fixed $j$, the leading contribution to the $j$-th moment of $\nu_N$ comes from choosing $j$ distinct unbarred indices and permuting them on the barred side. This gives $j!(N)_j/N^j\to j!$; repeated indices give $O_j(N^{-1})$. The limit moment sequence is that of the exponential distribution $e^{-y}\,dy$ on $[0,\infty)$. In the linear system defining the orthogonal polynomial, the limiting Gram matrix for weight $y^\delta e^{-y}\,dy$ is positive definite. Its coefficients and squared monic norm therefore converge. The limiting polynomial can be written
$$
 P(y)=(-1)^r e^y y^{-\delta}\frac{d^r}{dy^r}\big(e^{-y}y^{r+\delta}\big).
$$
Integration by parts proves its orthogonality, since the boundary terms vanish and the $r$-th derivative of every lower-degree polynomial is zero. By the same integration by parts against $y^r$, its squared norm is $r!\int_0^\infty e^{-y}y^{r+\delta}dy=r!(r+\delta)!$. This proves the limit. $\square$ [Classical Gauss quadrature](https://dlmf.nist.gov/3.5) · [Laguerre polynomials and orthogonality](https://dlmf.nist.gov/18.3)

The theorem bounds the balanced coefficient $a_m(Z)$ from below by $-(\lfloor m/2\rfloor!\,\lceil m/2\rceil!+o(1))N^{-m}$. This improves the use of Jensen alone. Equality in the scalar problem does not supply an exchangeable phase vector with the requisite coordinate marginals. Theorem 1 realizes the asymptotic scalar optimum for $m=2$.

## 4. Product-test rigidity and total-variation separation

**Theorem 3.** If a fixed $n$-coordinate phase law admits exchangeable extensions for arbitrarily large $N$ with two-coordinate product Haar marginals, it is product Haar. Quantitatively, if $N\ge n$ is one such extension length and $f_j: \mathbb T\to\mathbb C$, $|f_j|\le1$, are measurable, then
$$
 \left|\mathbb E\prod_{j=1}^n f_j(Z_j)-\prod_{j=1}^n\int f_j\,d\mathrm{Haar}\right|
 \le \frac{3n(n-1)}{2N}.
 \tag{6}
$$

*Proof.* Let $X_j=N^{-1}\sum_i f_j(Z_i)$ and $u_j=\int f_j\,d\mathrm{Haar}$. By pairwise independence, $\mathbb E|X_j-u_j|^2\le1/N$. The expectation of $\prod_j X_j$ corresponds to sampling indices with replacement. Conditional on no collision it equals the left expectation in (6) by exchangeability. The collision probability is at most $n(n-1)/(2N)$, so the difference of the two expectations is at most $n(n-1)/N$. To compare $\mathbb E\prod_j X_j$ with $\prod_j u_j$, Taylor-expand $\prod_j(u_j+t(X_j-u_j))$ on $[0,1]$. The linear term has expectation zero. Each remaining factor has modulus at most one throughout the line segment. Cauchy–Schwarz bounds the expectation of each pair of differences in the second derivative by $1/N$, giving the remaining $n(n-1)/(2N)$. Letting $N\to\infty$ for a fixed law and taking indicator functions determines every measurable rectangle, hence the law. $\square$ [Diaconis–Freedman, finite exchangeable sequences](https://projecteuclid.org/download/pdf_1/euclid.aop/1176994663)

**Theorem 4.** For every $m\ge2$ and $N\ge2m$, some $Z\in\mathcal E_{m,N}$ has exactly the independent phase responses at all even orders $2,4,\ldots,2m$ for every amplitude vector and every coordinate face, while its $2m$-coordinate marginal is singular with respect to product Haar. Smooth strictly positive exchangeable laws can preserve every one of these observations while their $2m$-coordinate marginals have total variation distance from product Haar arbitrarily close to one.

*Proof.* Set $s=2m-1$. Take independent Haar variables $U_0,\ldots,U_{s-1}$ in $\mathbb R/\mathbb Z$ and form
$$
 Z_i=\exp\big(2\pi i\sum_{j=0}^{s-1}i^j U_j\big),\qquad 1\le i\le N.
$$
The map to any $s$ chosen coordinates is an integer Vandermonde torus map with nonzero determinant, hence is surjective and pushes Haar to Haar. All weaker marginals are likewise product Haar. Consider a phase character with charges $\alpha_i-\beta_i$ where $\sum_i\alpha_i=\sum_i\beta_i=\ell\le m$. Its expectation vanishes unless the corresponding two multisets of indices have equal power sums through degree $s-1$. Since $s-1\ge m$, their first $\ell$ power sums are equal. Newton's identities over the rationals give equality of their elementary symmetric functions and then equality of the multisets. Consequently only the same diagonal terms as in the independent expansions survive. Uniformly permuting the coordinates makes the law exchangeable and retains these properties.

For any $2m$ coordinates their law is a finite mixture from the permutation step, supported on images of $s$-dimensional tori in a $2m$-torus. The images are compact subgroups of dimension at most $s$, hence Haar-null. Let their finite union be $C$. Independent smoothing in the circle does not change the vanishing of any Fourier moment because the character moments are multiplied by a factor from the independent smoothing variables. It retains every stated Haar marginal. With a smooth, strictly positive approximate identity the output density has the same properties. For any $\varepsilon>0$, take an open neighborhood $O$ of $C$ of Haar measure below $\varepsilon$. Compactness ensures that sufficiently small coordinate perturbations of every point of $C$ lie in $O$. The smoothing can therefore give $O$ probability exceeding $1-\varepsilon$. The total variation distance is at least $1-2\varepsilon$. $\square$

The two results concern different metrics on the response family. Each fixed product test becomes accurate as the extension length increases. Even exact knowledge of all the indicated moment responses and low marginals fails to distinguish specific laws separated almost maximally in total variation. This is consistent with finite de Finetti approximation, which compares to mixtures of product laws.

## 5. Conjectures and tests

**Higher-order sharpness conjecture.** For each fixed $m\ge3$,
$$
 \lim_{N\to\infty}N^m\min_{Z\in\mathcal E_{m,N}}a_m(Z)
       =-\lfloor m/2\rfloor!\,\lceil m/2\rceil!.
$$
Theorem 2 gives the lower bound, and Theorem 1 settles the corresponding case $m=2$. An asymptotically optimal construction would have to make $\mathbb E[Y^\delta P_N(Y)^2]\to0$ while enforcing the exact high-order product Haar marginals. The explicit Gauss–Radau nodes give a proposed limiting law for $Y$. To test impossibility, look for any valid inequality involving additional symmetric statistics whose marginal values are fixed but whose value conflicts with this limiting law.

**Fourth-order equality question.** Determine the $N$ for which a three-wise Haar, exchangeable vector can be supported on $|\sum_i Z_i|=\sqrt N$. Theorem 1 rules out $N=4,5$, settles the asymptotic optimum, and gives exact equality in an auxiliary finite phase alphabet. The unresolved condition in the circle model is exact support on the prescribed energy level, instead of convergence to it.

**Positive endpoint conjecture.** The limit $\lim_{N\to\infty}N\max_{Z\in\mathcal E_{2,N}}a_2(Z)$ exists. Determine its exact value. If it exists, the four-phase construction and bound (2) place it in $[32/\pi^4,1/2]$. Exact continuous Haar marginals prevent finite equality in (2). Whether they cause a strict gap in the asymptotic constant remains open in this development.

These are written proofs. Exchangeability, Gauss sums, and Gauss quadrature are established theories. The results here connect them through explicit extremizers and tests for the same partially observed phase response. Publication priority is provisional.
