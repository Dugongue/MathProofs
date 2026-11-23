# Simultaneous concavity profiles of one analytic phase law

A phase law is a probability measure $\mu$ on $\mathbb T^n$, with coordinates $\xi_j=e^{i\theta_j}$. For $m\ge2$, use the phase-moment response
$$
 F_{\mu,m}(x)=\mathbb E_\mu\left|\sum_{j=1}^n x_j^{1/(2m)}\xi_j\right|^{2m},
 \qquad x\ge0.
$$
A strict Jensen witness consists of rational $x,y,\lambda$, where $0<\lambda<1$, such that the concavity inequality at $\lambda x+(1-\lambda)y$ is strictly violated. These witnesses retain the same state input when the experiment changes. The problem is to classify the families of witness-existence languages seen at all probes at once.

## 1. One four-coordinate analytic law for a countable family of probes

Let $A_h$ average a law over the rotations by $2\pi j/h$ of the first phase coordinate, $0\le j<h$. Define the probe $p=(h,m)$ to ask whether $F_{A_h\mu,m}$ has a strict Jensen witness. The experiments admit the refinement order
$$
 (h,m)\preceq(h',m')\quad\Longleftrightarrow\quad h'\mid h,\quad m\le m'.
$$
Indeed if an experiment records the moment functions at all complex amplitudes through order $2m$, then the coarser experiment is recovered by changing the first amplitude phase, averaging over the coarser cyclic group and dropping higher orders. The decision question uses the real nonnegative-amplitude slice at the specified order. On Fourier characters $e^{iv\cdot\theta}$, the averaging operator retains the character exactly when $h\mid v_1$, by summing a finite geometric series.

**Theorem 1.** Put
$$
 \mathcal P=\{(h,m):m\ge2,\ 1\le h\le m\}\setminus\{(2,2)\},
$$
ordered by the displayed refinements. For every uniformly computably enumerable family $S_p\subseteq\mathbb N$ on $\mathcal P$ with $S_p\subseteq S_{p'}$ whenever $p\preceq p'$, there is one uniformly computable family of strictly positive real-analytic densities $\rho_e$ on $\mathbb T^4$ such that
$$
 F_{A_h\mu_e,m}\text{ is nonconcave}
 \quad\Longleftrightarrow\quad e\in S_{(h,m)} .
$$
All three-coordinate marginals are product Haar, and all proper coordinate faces have exactly the independent response at every probe. The densities can be made uniformly as close to Haar as desired in sup norm. They have a shared holomorphic extension strip and an effective common tail bound. At a negative probe a finite witness code gives an explicit rational Jensen violation, and these codes transport by inclusion along the refinement arrows. Outside $\mathcal P$ the response is independent for every four-coordinate law with product Haar triples.

**Proof.** For a balanced integer Fourier charge $v$ with $\sum_i v_i=0$, put $q(v)=\sum_i(v_i)_+$ and let $|v|$ be the vector of componentwise absolute values. Its contribution to the order-$2m$ moment first appears at $q(v)\le m$. To see the exact weights, write the two multi-indices in the expansion as $v_++\gamma$ and $v_-+\gamma$, with $\gamma\ge0$ and $|\gamma|_1=m-q(v)$. The monomial has exponent $(|v|+2\gamma)/(2m)$ and weight
$$
 \frac{(m!)^2}{\prod_i (|v_i|+\gamma_i)!\gamma_i!}.
 \tag{1}
$$
This weight is a positive integer, the product of two multinomial coefficients. The charges $v,-v$ have the same weight.

For each $(d,q)\in\mathcal P$, choose the balanced charge
$$
 v_{d,q}=
 \begin{cases}
 (d,q-d,-1,-(q-1)),&d<q,\\
 (q,-1,-1,-(q-2)),&d=q\ge3 .
 \end{cases}
$$
It has full support, positive mass $q$, first coordinate $d$ and third coordinate $-1$. The charges are distinct even up to sign, since the first coordinate is positive and the positive mass is determined by the charge.

Fix a rational $0<\eta\le1$. If $e$ first appears in $S_{(d,q)}$ at stage $t$ of a single joint enumeration, set $a_{e,d,q}=\eta\,2^{-10q-t-1}$, and set it to zero if no first stage exists. Use the common density
$$
 \rho_e(\theta)=1-\sum_{(d,q)\in\mathcal P}
                  a_{e,d,q}\cos(v_{d,q}\cdot\theta).
 \tag{2}
$$
The total coefficient sum is at most $\eta\sum_{q\ge2}q\,2^{-10q-1}<\eta/2$. Each cosine integrates to zero and loses its Fourier coefficient upon forgetting any one coordinate. Thus (2) gives positive probability densities with product Haar triples. On the complex strip $|\operatorname{Im}\theta_i|<1$, a summand has magnitude at most $a_{e,d,q}e^{2q}$. Summation gives an effective geometric tail on this strip. A coefficient can be approximated by running the enumeration to a prescribed time, since every later contribution is bounded by the corresponding dyadic factor. Truncating in $q$ and time therefore gives uniform computability with a sup-norm error bound.

At $(h,m)$, a mode $(d,q)$ contributes precisely when $h\mid d$ and $q\le m$. Its conjugate pair contributes nonpositive coefficients to the real response because of (1) and (2). If no mode with positive amplitude contributes, the response is $F_{0,m}$. The independent response is a nonnegative sum of weighted geometric means and hence concave. If a mode contributes, take the term for $\gamma=(0,m-q,0,0)$. It has coefficient at most $-a_{e,d,q}$, and its exponent in $x_3$ is $1/(2m)$. Holding the other coordinates at one gives a perturbation with a negative coefficient at that power. No other mode can contribute positively there. The independent terms with positive exponent in this coordinate start at $1/m$, so they are dominated in second derivative near zero. The response is not concave. By the stated language monotonicity, the existence of any contributing mode with positive amplitude is equivalent to $e\in S_{(h,m)}$. Its converse uses the mode at $(h,m)$ itself. Every perturbation term has full support, so faces missing any coordinate are independent.

For the last assertion, product Haar triples kill every nonzero Fourier charge with any zero coordinate. All charges visible in order $2m$ have $|v_1|\le m$, so none survive when $h>m$. At $m=2$, full support forces every absolute charge to be one, so $h=2$ also kills every perturbation. Conversely each remaining cell has one of the explicit full-support charges.

**Witness transport.** A code is a triple $(d,q,t)$ asserting the verifiable first enumeration at stage $t$ and the probe conditions $h\mid d,\ q\le m$. These conditions are preserved under $p\preceq p'$, so the same code transports, with identity and composition automatic. It has a fixed computable interpretation as a rational Jensen violation at each accepting probe. Set coordinates 1, 2, and 4 to one and vary the third coordinate. Compare the slices at $x_3=0,t_0$ and their midpoint, where
$$
 t_0=\left(\frac{a_{e,d,q}}{8\,4^{2m}}\right)^{2m}.
$$
Writing the concavity gap as the midpoint value minus the average endpoint value, the independent gap is at most $4^{2m}t_0^{1/m}$. The particular negative monomial contributes a gap at most $-\tfrac14 a_{e,d,q}t_0^{1/(2m)}$, since $2^{-1/(2m)}-\tfrac12>1/4$. All other perturbation terms have nonpositive gaps. This is a strict violation by the choice of $t_0$. Thus the transported code always computes a witness, rather than only indicating that the decision stays negative. When only the averaging order changes, every existing rational witness also transports literally, because the finer probe adds only negative multiples of concave monomials. The code is unchanged when the order $m$ grows, even though its evaluated amplitudes can change. $\square$

**Exact effective scope.** In the class of uniformly computable densities of the form (2) with nonnegative coefficients, all probe nonconcavity profiles are uniformly c.e. and monotone. One can enumerate rational witnesses and approximate their gaps until a strict violation is certified. The computation uses the effective law description, uniform approximation of the bounded continuous moment integrands and continuity on the orthant. If a response is nonconcave, some rational witness exists by density and strictness. Alternatively, with uniformly computable nonnegative coefficients one can directly enumerate the finitely many potentially visible positive amplitudes. The monotonicity follows from the finite Fourier characterization above. This gives the converse classification in the specified class.

The theorem uses a fast approximation name for the density, with a common analytic bound. It does not assume a list of exact nonzero Fourier coefficients is supplied. A finite list with explicit rational coefficients gives a different input representation, for which the negative-coefficient probe test is decidable by inspecting the list. The proof realizes nonrecursive c.e. profiles even though each individual nonzero Fourier coefficient in (2) is dyadic times a fixed rational. [Weihrauch, computable real and function representations](https://link.springer.com/book/10.1007/978-3-642-56999-9)

If all full complex-amplitude moments through order $2M-2$ must also match independence, take $S_{(h,m)}=\varnothing$ for $m<M$. Omitting modes with $q<M$ gives any monotone c.e. profile satisfying this constraint on the upper part of the grid. The single coordinate face where failure can occur remains the same.

## 2. Witness precision records quantitative information

Normalize witness endpoints to the simplex $\sum_i x_i=1$, and let the bit depth be the maximum bit length of a reduced denominator of any endpoint coordinate or of $\lambda$. For a negative probe in Theorem 1, let $a_*$ be the maximum of its finitely many visible amplitudes $a_{e,d,q}$.

**Proposition 2.** For fixed $m$, the minimum rational witness bit depth is
$$
 \Theta_m\bigl(1+\log_2(1/a_*)\bigr).
$$
The constants are uniform in $h,e$ and the language family.

The explicit endpoint calculation with a mode of amplitude $a_*$ gives the upper bound. Normalize the two endpoints by their sums $U,V$, and use the interpolation weight $U/(U+V)$ on the normalized first endpoint. Degree-one homogeneity multiplies the midpoint gap by $2/(U+V)$, preserving the strict violation. The endpoints and new weight are rational of the claimed bit depth. This conclusion works also for non-dyadic amplitudes by using a rational lower approximation within a factor two to the positive maximum.

For the lower bound, $F_{0,m}$ is strongly concave on the simplex. In an interior tangent direction $w$, the independent term supported on $i,j$ with multiplicities $m-1,1$ contributes at least
$$
 (m-1)x_ix_j(w_i/x_i-w_j/x_j)^2
$$
to the negative Hessian, because $x_i^{(m-1)/m}x_j^{1/m}\ge x_ix_j$. Summing over pairs gives $(m-1)\sum_i w_i^2/x_i\ge(m-1)\|w\|_2^2$, using $\sum_i w_i=0$. Thus the independent Jensen gap is at least
$$
 \tfrac12(m-1)\lambda(1-\lambda)\|x-y\|_2^2 .
$$
Continuity gives this also at the boundary. At bit depth $L$, distinct endpoints differ in a coordinate by at least $2^{-2L}$, and $\lambda(1-\lambda)\ge2^{-2L}$. The independent gap is at least $(m-1)2^{-6L}/2$. Meanwhile the absolute sum of all perturbation coefficients is at most $4^{2m}a_*$, by the multinomial sum and the bound $a_*/2$ on each contributing Fourier moment. The perturbation's absolute Jensen gap is at most twice this quantity, since every monomial is at most one on the simplex. To violate concavity requires $2\cdot4^{2m}a_*>(m-1)2^{-6L}/2$. This yields the lower bound.

In particular, there is no total computable bound on the minimum bit depth at every accepting input of a probe whose language in Theorem 1 is nonrecursive. Such a bound would give a positive computable lower threshold on $a_*$ for every accepting input, from the preceding inequality, while $a_*=0$ on every other input. Approximation to less than half the threshold would then decide the language. This precision obstruction survives an arbitrarily small fixed cap on the sup-norm distance of the densities from Haar.

## 3. Exact finite signed profiles at one common moment order

The countable theorem uses increasing moment order to reach new Fourier frequencies. A complementary statement fixes one order, keeps every proper marginal and every lower moment at its independent value, and prescribes exact signed strengths on **arbitrary finite posets** rather than only the divisibility grid.

**Theorem 3.** Given any nonempty finite poset $P$, there are $m=\max(3,|P|)$, a single integer torus direction $w\in\mathbb Z^{2m}$, and cyclic averages $B_p$ in that direction, indexed by $P$, with the following properties.

1. The averaging operators encode the order exactly: $B_pB_q=B_p$ if and only if $p\le q$.
2. There is a constant $\delta>0$ depending only on $P$ such that for any $g:P\to[-1,1]$ one strictly positive trigonometric polynomial density $\rho_g$ on $\mathbb T^{2m}$ has
   $$
   F_{B_p\mu_g,m}(x)=F_{0,m}(x)-\delta g(p)\prod_{i=1}^{2m}x_i^{1/(2m)}.
   $$
   Every proper marginal is product Haar, and all lower moments equal those of Haar even for complex amplitudes. The construction is uniform for computable $g$.
3. Concavity fails at exactly the probes with $g(p)>0$, and then only on the full coordinate face. If $g$ is increasing on $P$, every rational strict Jensen witness for $p$ is also a witness for $q$ when $p\le q$, with literally the same amplitudes and interpolation weight.

To prove this, index the elements of $P$ by $j\le |P|$ and select distinct primes $\ell_j$. Let $D_j=\prod_{v\ge j}\ell_v$ for original indices and set $D_j=0$ on the $m-|P|$ auxiliary indices. Thus $D_p\mid D_q$ for original indices precisely when $q\le p$. Put $H=\sum_{j=1}^m D_j$ and $u_j=(m-2)D_j-H$. On the $j$-th coordinate pair of the torus choose the direction entries $(u_j,0)$. For each original $j$, let $v_j\in\{1,-1\}^{2m}$ have sign pair $(1,-1)$ on the $j$-th pair and $(-1,1)$ on all other pairs. The $v_j$'s are balanced and distinct up to sign, since $m\ge3$. Their frequencies in direction $w$ are
$$
 \langle w,v_j\rangle=2u_j-\sum_i u_i=2(m-2)D_j.
$$
Average on rotations $2\pi t/[2(m-2)D_p]$ along $w$. Then the mode $v_j$ survives at $p$ exactly when $j\le p$. If $p\le q$, the group for $q$ is a subgroup of the group for $p$, so $B_pB_q=B_p$. Conversely apply this identity to the $v_p$-mode. It survives $B_q$ only when $p\le q$, giving the order reflection even if the circle action has a kernel.

Choose the real coefficients $b_j$ with $\sum_{j\le p}b_j=g(p)$ by finite triangular inversion on the poset. Their absolute sum has a uniform bound $K_P$ for all $|g|\le1$. Choose $\delta>0$ sufficiently small and use
$$
 \rho_g(\theta)=1-\frac{\delta}{(m!)^2}\sum_j b_j\cos(v_j\cdot\theta).
$$
The bound on the coefficient sum gives strict positivity, and integrating a proper marginal kills every term. Positive charge mass $m$ gives the lower-moment claim. At order $2m$ the absence of any repeated overlap and the unit absolute charges give the one common monomial, with coefficient $-\delta b_j$ for each surviving mode. This proves the displayed formula. A nonnegative total monomial coefficient preserves concavity. A negative coefficient gives the boundary derivative or Jensen witness from Theorem 1. Finally, when $g(q)\ge g(p)$, the difference of the responses is a nonpositive multiple of one concave geometric mean, so it can only decrease any concavity gap. This gives the literal witness inclusion. [Rota, finite-poset inversion](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rota1.pdf)

In contrast to the witness code formulation when moment order varies, the fixed-order family gives inclusion of the complete rational witness sets. Signed $g$'s need not be monotone: they show that the underlying geometric law can be arbitrary across these observed regimes even though the *observations* admit the exact poset refinements. Monotone nonnegative $g$'s give an explicit subclass with natural counterexample transport. Taking $g_e(p)$ to be the small sum of dyadic first-enumeration amplitudes at all $q\le p$ implements every monotone c.e. finite family at a common order as well.

## Scope

These are written proofs. Exact integer controls verified 5,048 charge tuples and 26,705 divisor gates from 1,099 finite relation presentations. Theorem 1 keeps the number of coordinates fixed at four while its probes vary in averaging and moment order. Theorem 3 has one exact common response shape per input across the finite experiment. Both results concern existence of strict Jensen witnesses, with the opposite concavity verdict its complement. The use of a common analytic density, actual averaging postprocessing, and transport of executable witnesses links the original phase-moment construction to the shared-input notion of simultaneous computability. The earlier phase theorem constructs failure faces within one experiment, and the earlier arithmetic finite-poset theorem concerns integral witnesses. Here the probes are analytic transformations of one law and the certificates are explicit inequalities. [Phase-moment antecedent](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md) · [Simultaneous computability definition and arithmetic probes](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/SimultaneousComputability.md)
