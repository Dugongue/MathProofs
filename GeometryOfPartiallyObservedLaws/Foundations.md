# Foundations of the geometry of partially observed laws

A mathematical response can obey a shape law for every state compatible with the available measurements, for none of them, or for some and not others. The field studies that three-valued profile as the measurements change, together with the size of the uncertainty, the geometry of failures, and the observations needed to settle the law.

The starting example is a phase moment. Its possible failure sets include all uniform hypergraphs even when every smaller marginal and lower moment matches independence. The theory below treats observation, response, and law as separate arguments. This makes it possible to compare the same observations under different laws and to study the entire response at once. [Original definition and uniform obstruction theorem](https://github.com/Dugongue/MathProofs/blob/990ed5ac8b956f82c10370d60b7bd54aa4ad5568/FourFieldProposals/PartiallyObservedLaws.md)

## 1. Objects and operations

**Definition 1 (observed response system).** A system consists of a state set $M$, a collection of probes $P_i:M\to Y_i$, a family of jointly permitted probe sets with a monotone cost, a response $F:M\to V$, and a collection of laws $L\subset V$. For a feasible trace $y$ on a permitted set $I$, define
$$
 M_I(y)=\{m:P_I(m)=y\},\qquad C_I(y)=F(M_I(y)).
$$
The law is **forced** if $C_I(y)\subset L$, **excluded** if $C_I(y)\cap L=\varnothing$, and **undetermined** otherwise. A law certificate is a permitted set yielding one of the first two verdicts. A minimal certificate is inclusion-minimal. The observation cost of that verdict is the infimum of the costs of such sets, given the compatible traces of a fixed actual state. Empty fibers are treated as inconsistent data, separately from the three law verdicts.

For response spaces of functions on $U$, a regional law is indexed by a subset of $U$. The regional failure family of a fixed response contains all regions on which its restricted response fails the law. For laws inherited by restriction, this family is upward closed. Its inclusion-minimal elements are the minimal failure regions. These refer to where the response fails, while minimal certificates refer to what was observed. The phase-moment theorem connects both notions without identifying them.

**Definition 2 (refinement and recoding).** A probe $Q$ refines $P$ when $P$ factors through $Q$. A recoding is an invertible state and response reparametrization that respects probe refinement, allowed sets and costs, and carries each law to its counterpart. Law profiles and their costs are invariants of recoding. A simulation may have a noninvertible state map. To pull a forced verdict back, the simulations of observations and responses must carry every compatible source state to a compatible target state and must reflect the law on its response image. Exact verdict transfer in both directions requires that the image of the compatible source responses meets the same law and failure sets as the whole compatible target family. Surjectivity on that family suffices.

**Lemma 3 (refinement).** At consistent traces of the same state, a forced or excluded verdict survives further observations. An undetermined verdict can change in either direction. The certificate sets for either settled verdict form an upper set in the refinement order.

*Proof.* Refinement shrinks the compatible response family. Both disjointness and containment are inherited by its nonempty subsets.

**Definition 4 (affine model and law margins).** In a classical affine model, states are probability laws and a probe specifies expectations, often all bounded tests of a measurable marginal. The response is a collection of expectations. A closed convex law in a finite-dimensional response space can be represented by affine inequalities, each called a law test. For concavity these are the Jensen inequalities, with one test for each chord and interpolation parameter. In a quantum affine model, states are density matrices, probes give prescribed expectation values or partial traces, and responses are expectations of Hermitian observables. A *margin* for a test is the right-hand side minus the expected test observable. The geometry depends on the permitted probe spans and on the margins.

These objects include known identified sets and moment problems. The additional organizing questions concern an entire collection of laws, where their failures occur, and the information cost of certifying them under comparable observation models. Convex support functions and partial identification are existing foundations. [Beresteanu–Molchanov–Molinari](https://cemmap.ac.uk/publication/partial-identification-using-random-set-theory/) · [Bertsimas–Popescu](https://doi.org/10.1137/S1052623401399903)

## 2. Exact local geometry in classical and quantum models

Fix a reference probability $\lambda$. Let $A$ be the closed real subspace of $L^1(\lambda)$ spanned by the constant $1$ and all tests imposed by the observed probes. In the case of a pushforward marginal, these tests are the bounded functions pulled back from the probe space. The observed values are the reference values. At radius $0\le r\le1$ consider exactly the states
$$
 d\mu=(1+h)d\lambda,\qquad \|h\|_\infty\le r,\qquad \int ah\,d\lambda=0\quad(a\in A).
\tag{1}
$$
These conditions enforce nonnegativity, normalization, and the observations. They permit perturbations of either sign. This choice of local uncertainty is part of the model.

**Theorem 5 (exact support and robustness).** For every $g\in L^1(\lambda)$, the attainable interval for its centered expectation in (1) is
$$
 [-r d_A(g),r d_A(g)],\qquad d_A(g)=\inf_{a\in A}\|g-a\|_1 .
\tag{2}
$$
For $g_1,\ldots,g_d$ the centered attainable region is compact and convex, with support in direction $c\in\mathbb R^d$ equal to $r d_A(\sum_j c_jg_j)$. In particular (2) determines all joint trade-offs. For any family of law tests $\int g_t\,d\mu\le b_t$, set $\delta_t=b_t-\int g_t\,d\lambda$. The law is forced at radius $r$ exactly when
$$
 \delta_t\ge r d_A(g_t)\quad\text{for every }t.
\tag{3}
$$
If the reference obeys the law, its largest guaranteed radius in $[0,1]$ is
$$
 \min\left(1,\ \inf_{t: \,d_A(g_t)>0}\frac{\delta_t}{d_A(g_t)}\right),
$$
where the infimum of an empty collection is $+\infty$. If the reference passes a test with equality and $g_t\notin A$, there are strictly positive compatible densities arbitrarily close to it that fail the test.

*Proof.* The dual of the quotient $L^1(\lambda)/A$ is isometrically the annihilator $A^\perp\subset L^\infty(\lambda)$. A norming functional on the line generated by the coset of $g$ extends to the quotient by Hahn–Banach. Its representative $h$ may be scaled to norm at most $r$, and its negative gives the other endpoint. Intermediate values follow by convexity. The perturbation set is weak-star compact and the $g_j$ are continuous for that topology. Apply the same result to $\sum_j c_jg_j$. The law holds for all compatible states exactly when every test passes at its worst allowed expectation. This gives (3) and the radius formula. For a tight test, take any $0<r<1$ and use the positive maximizing perturbation. The new density has lower bound $1-r$. $\square$

**Corollary 6 (what identifies what).** With any positive radius in (1), an expectation is locally identified exactly when $g\in A$. Thus two observation schemes have identical identification for every integrable expectation if and only if their closed observed subspaces agree. Their exact local uncertainty for all finite response vectors then agrees. When the spans are properly nested, a one-dimensional response separates the two schemes.

*Proof.* Apply (2) and use closedness of the span. A point in the larger span outside the smaller one has a positive quotient norm for the smaller span. $\square$

**Theorem 7 (quantum version).** Fix a strictly positive density matrix $\rho_0$, and let $A$ be the real span of $I$ and the Hermitian observables measured by the probes. The state neighborhood
$$
 \rho=\rho_0^{1/2}(I+H)\rho_0^{1/2},\qquad
 H=H^*,\quad \|H\|_{\rm op}\le r,\qquad
 \operatorname{Tr}\left(H\rho_0^{1/2}A'\rho_0^{1/2}\right)=0\ \ (A'\in A)
$$
has the same support, joint trade-off and robustness formulas with
$$
 d_A(G)=\inf_{A'\in A}\big\|\rho_0^{1/2}(G-A')\rho_0^{1/2}\big\|_1 ,
\tag{4}
$$
where the norm is the trace norm. At $\rho_0=I/D$ for dimension $D$, the norm is $D^{-1}$ times the unweighted trace norm.

*Proof.* The trace pairing identifies the real dual of Hermitian matrices with trace norm with Hermitian matrices with operator norm. This follows by diagonalization and the sign matrix of a Hermitian matrix. Apply the same quotient duality as in Theorem 5 to the weighted observable subspace $\rho_0^{1/2}A\rho_0^{1/2}$. Positivity and trace one follow from the operator interval and the observation of $I$. The other formulas follow from support functions. $\square$

For instance at the maximally mixed two-qubit state, observing both single-qubit marginals does not identify the expectation of $X\otimes X$, where $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$. Its exact local interval is $[-r,r]$. The maximizing perturbation is $H=r X\otimes X$, and the upper bound follows from the choice $A'=0$ in (4). This demonstrates joint uncertainty even when whole subsystem states are known.

### Finite noisy probes

**Proposition 8 (exact price of noisy measurements).** Let $A_0$ be a closed observed span of exact tests containing $1$, and let $a_1,\ldots,a_m$ be additional tests in $L^1(\lambda)$. Replace their exact centered values by the constraint $\|(\int a_jh)_j\|\le \varepsilon$ for some norm on $\mathbb R^m$. If $r,\varepsilon>0$, the worst centered expectation is
$$
 \inf_{u\in\mathbb R^m}
 \left[r\,d_{A_0}\!\left(g-\sum_j u_ja_j\right)+\varepsilon\|u\|_*\right].
\tag{5}
$$
The same formula holds in the finite-dimensional quantum model with (4). The infimum equals the primal maximum, including when some measured tests are redundant.

*Proof.* Write $K$ for the compact convex set of pairs $(s,t)$ obtained from $(\int a_jh,\int gh)$ in the exact neighborhood for $A_0$. By homogeneity the center $h=0$ is feasible with $s=0$. The support problem is the maximum of $t$ subject to $(s,t)\in K$ and $s$ in the $\varepsilon$-ball. Introduce the second copy $z$ of $s$ in the ball. The compact convex image of $K$ times the ball in coordinates $(s-z,t)$ has $0$ interior to its first-coordinate projection because $K$ contains $(0,0)$. The upper boundary's supporting hyperplane over $s-z=0$ can therefore be chosen with last coefficient positive. Normalize it to one, with first coefficient $-u$. The support becomes the sum of the support of $K$ in direction $(-u,1)$ and the support of the ball in direction $u$. Formula (2) computes the former. Weak duality holds for every $u$ by the dual norm inequality, so the two bounds agree. The same finite-dimensional argument on the response image applies to (4). $\square$

## 3. Product structure, hidden interactions, and how observations compose

Let $X=\prod_{i=1}^n X_i$ with product reference probability $\lambda$. Fix a nonempty family of observed coordinate subsets $P_j\subseteq[n]$. Let $D$ be their downward closure, adding the empty set. For a coordinate $i$, let $E_i$ average over $X_i$ while keeping the other coordinates fixed. The $E_i$ are commuting contractions on $L^1$ and $L^\infty$. Define the interaction component indexed by $S\subseteq[n]$ by
$$
 g_S=\Pi_Sg,\qquad
 \Pi_S=\prod_{i\in S}(I-E_i)\prod_{i\notin S}E_i .
\tag{6}
$$
It depends only on $S$ and has zero average in each coordinate in $S$. The projections have pairwise disjoint ranges in the algebraic sense $\Pi_S\Pi_T=0$ for $S\ne T$. Their sum is the identity. The decomposition is valid for all integrable responses in (6).

**Theorem 9 (exact visibility of interactions).** The observed space for these marginals is $\operatorname{im}\sum_{S\in D}\Pi_S$. Accordingly an expectation is pinned at the product trace in (1) exactly when $g_S=0$ for every $S\notin D$. Quantitatively,
$$
 \max_{S\notin D}2^{-|S|}\|g_S\|_1
       \ \le\  d_A(g)\ \le\ \sum_{S\notin D}\|g_S\|_1 .
\tag{7}
$$
On a finite product with $|X_i|=d_i$ and fully supported factors, the dimension of the hidden subspace is
$$
 \sum_{S\notin D}\prod_{i\in S}(d_i-1).
\tag{8}
$$
On a finite quantum product at the maximally mixed state there is the same visibility criterion for Hermitian observables, with normalized partial traces as $E_i$ and with $d_i^2-1$ in (8).

*Proof.* A function of the coordinates of $P_j$ lies in the sum of the interaction spaces on its subsets. Each included interaction space conversely consists of integrable functions of some observed set. Such functions are approximated in $L^1$ by bounded probes. The finite sum of the $\Pi_S$ over $D$ is a bounded projection, so its image is closed and equals $A$. For $S\notin D$, choose $\phi=\operatorname{sign}(g_S)$. The probability product makes $\Pi_S$ self-adjoint under the $L^1,L^\infty$ pairing, and $\|\Pi_S\phi\|_\infty\le 2^{|S|}$. Thus $2^{-|S|}\Pi_S\phi$ is an admissible unit perturbation in $A^\perp$, attaining $2^{-|S|}\|g_S\|_1$. The visible projection is a candidate in the infimum giving the upper bound. Formula (8) follows by tensoring the decomposition into constants and zero-mean functions at each coordinate. In the quantum case, average each matrix factor by normalized partial trace and replace constants by scalars times identity. These maps are commuting self-adjoint projections under trace pairing. Tensoring the scalar and traceless Hermitian real spaces gives the quantum formula. $\square$

**Corollary 10 (independent completion versus arbitrary joint completion).** Suppose the complete marginal laws on disjoint blocks $B_1,\ldots,B_\ell$ are fixed and the reference is their product. For a real expectation $g$, the independent value agrees with all arbitrary joint completions in (1) exactly when $g$ is a sum of integrable functions of the individual blocks, up to equality almost everywhere. If this agreement holds, it holds also for every compatible joint completion absolutely continuous with respect to the reference. For general completions, including singular ones, the implication to all joint completions holds if the additive identity holds pointwise. In finite fully supported products the two assertions coincide. A nonzero interaction involving two or more blocks gives distinct joint values arbitrarily close to the product from both sides.

*Proof.* Apply Theorem 9 to the block product as the product of the $X_i$. Only the empty and singleton-block components are visible. For such an additive representative the value follows directly from the marginal expectation formula. A nonzero hidden component gives two-sided perturbations by (7). $\square$

This caveat about singular joint laws is necessary. For two uniform continuous marginals, the indicator of the diagonal equals zero almost everywhere for their product but has expectation one under the diagonal coupling. Thus an almost-everywhere statement in a local norm does not automatically assert global agreement of every model completion.

## 4. Every monotone certificate pattern, with an exact interaction cost

Fix $m$ named probes and a single law $\mathbb E g=\mathbb E_\lambda g$, at a finite fully supported product reference. Its **access structure** consists of the subsets of probes whose reference trace forces that equality. Denote by $\mathcal B$ the inclusion-maximal subsets not forcing the equality. This definition does not depend on whether “force” is tested in an arbitrarily small neighborhood (1) or in the whole finite fiber. If it holds locally, Theorem 9 writes $g$ as a sum of observable functions, which fixes the expectation for the whole fiber.

**Theorem 11 (access structure representation and sharp cost).** Every monotone Boolean function on $m$ probes occurs as the access structure for an exact scalar expectation at a fully supported independent binary reference. All traces can be ordinary coordinate marginals. In such a representation, count one for each nonempty index set $S$ with $g_S\ne0$, using (6). The smallest possible count across all finite full-support product representations equals the number of maximal unauthorized sets $|\mathcal B|$. In particular the upper bound can use only singleton interactions.

*Proof.* For each maximal unauthorized set $B\in\mathcal B$, introduce one unbiased binary coordinate $x_B$. Probe $j$ is the marginal on the coordinates $x_B$ with $j\notin B$. Take $g=\sum_{B\in\mathcal B} x_B$, viewing a bit as a sign. A set $J$ sees the coordinate $x_B$ precisely when it contains some $j\notin B$. By Theorem 9 the equality is forced exactly when $J$ sees every coordinate, that is, when $J$ is contained in no maximal unauthorized set. An unauthorized trace admits both the reference and arbitrarily close positive witnesses that violate the equality. The case of the constant true access function uses $g=0$, and the constant false case uses one unobserved coordinate.

For the lower bound in any representation, each nonzero interaction $g_S$ defines the set $B_S=\{j:S\nsubseteq P_j\}$, where $P_j$ is the coordinate set of probe $j$. Unauthorized probe sets are exactly the union of the principal ideals $\{J:J\subseteq B_S\}$. Each maximal element of the union is one of the $B_S$. Distinct maximal unauthorized sets thus require distinct interactions. The binary construction realizes equality. $\square$

**Corollary 12 (minimum cost is weighted set cover).** When the cost is additive across probes, the minimum cost to certify a given exact expectation at the independent trace is the minimum cost of a set cover of its nonzero interaction supports, with probe $j$ covering the supports contained in $P_j$. Every finite weighted set-cover instance with feasible cover is realized using only singleton interactions by taking one independent sign per universe element and a probe per offered set. In particular exact certification cost is NP-hard in an explicitly given classical product model. The combinatorial equality holds independently of the complexity claim.

This theorem distinguishes the visibility question from the classification of minimal regional failures. For equality at a product trace the observation side has an exact general representation and sharp interaction cost. For concavity, the observation and regional failure profiles can interact in ways that depend on a whole family of tests. [Phase-moment geometry](PhaseMoments.md) · [Finite certificates and observation costs](Inference.md)

## 5. Problems and falsifiable conjectures

1. **Decomposition norms on junction trees.** For a finite product with acyclic observed marginal scopes, compare the best norm sum in representations $a=\sum_j h_j(X_{P_j})$ with $\|a\|_1$. This norm sum prices per-probe calibration errors. The binary path has sharp scale $\sqrt m$ by Proposition 13 below, where $m$ is the number of scopes. A conjecture for arbitrary finite product alphabets and acyclic scopes is that there is a universal upper bound $C\sqrt m$, even with unbounded scope size. A sequence with a diverging ratio after division by $\sqrt m$ would disprove it.
2. **Finite shape certificates with a margin.** Fix the phase-moment order, restrict to $x_i\in[\eta,1]$, and bound the sum of absolute coefficients in the independent and perturbation responses after normalization. Suppose one only needs to separate concave responses from ones with a Jensen violation of size at least $\gamma$. Does there always exist a common grid of Jensen tests of size polynomial in the number of active coefficients, $n$, $\eta^{-1}$ and $\gamma^{-1}$? A negative answer would give a superpolynomial family of test regions each indispensable at a fixed inverse-polynomial margin. The case $\eta=0$ has singular derivatives and is a separate problem. [Phase-moment analysis](PhaseMoments.md)

**Proposition 13 (the sharp binary path scale).** In problem 1 for the uniform binary path, with $m=n-1$ and $n\ge2$, the largest decomposition-norm ratio is of order $\sqrt m$.

*Proof.* For the lower bound use the sum of the $m$ adjacent-pair characters. Each has coefficient one in its unique edge summand in every decomposition. That summand has $L^1$ norm at least one, while the sum has $L^1$ norm at most $\sqrt m$. Every observed $a$ is a linear combination of the constant, the $n$ singleton Walsh characters, and the $m$ adjacent-pair characters. Assign each character to one containing edge. This gives a decomposition with sum of $L^1$ norms at most the sum of the absolute coefficients, which is at most $\sqrt{2n}\|a\|_2$ by orthogonality and Cauchy–Schwarz. For a degree-at-most-two Walsh polynomial, the inequality $\|a\|_4\le 3\|a\|_2$ follows from the Bonami inequality. Interpolation $\|a\|_2\le\|a\|_1^{1/3}\|a\|_4^{2/3}$ yields $\|a\|_2\le9\|a\|_1$. This gives the asserted upper bound. $\square$ [Bonami's Fourier inequality](https://www.numdam.org/item/AIF_1970__20_2_335_0/)

The foundational results use existing convex duality, orthogonal interaction decompositions, and hypercontractivity. The proof suite isolates their consequences for an observation-law profile and gives the access representation, exact interaction cost, and common classical-quantum robustness formulas with their stated scopes. Literature priority for these formulations remains provisional.

## 6. From bounded densities to arbitrary compatible couplings

**Theorem 14 (simultaneous approximation by bounded-density completions).** Let the coordinate spaces be compact metric spaces with product reference $\lambda=\bigotimes_i\lambda_i$. Suppose every coordinate lies in an observed scope, and the observed marginals are the product reference marginals. For each $i$, choose a finite measurable partition of diameter at most $\eta$ on the support of $\lambda_i$ and let $b_i>0$ be the least mass among its positive-mass cells. Every compatible joint law $\mu$ has a compatible law $\nu\ll\lambda$ satisfying
$$
 0\le\frac{d\nu}{d\lambda}\le \min_{P\in D}\prod_{i\notin P}b_i^{-1}.
\tag{9}
$$
For any continuous $g$, $|\int g\,d\mu-\int g\,d\nu|\le\omega_g(\eta)$, where the modulus uses the maximum coordinate distance. In particular the supremum over bounded-density compatible laws equals the supremum over all compatible laws. An additive identity as in Corollary 10 almost everywhere suffices for agreement of continuous responses on the whole fiber.

*Proof.* Sample $x$ from $\mu$. In each coordinate independently resample from the corresponding reference law conditioned on the cell containing $x_i$. Cells of zero reference mass are never encountered, since every singleton is observed. For any observed scope $P$, its input marginal is $\lambda_P$ and the product resampling kernel preserves $\lambda_P$. Thus the output has all the prescribed marginals. On a product cell $C=\prod_i C_i$, the density is constant and equals $\mu(C)/\lambda(C)$. For $P\in D$, $\mu(C)\le\prod_{i\in P}\lambda_i(C_i)$, which gives (9). The coupling between $x$ and its resample moves each coordinate by at most $\eta$, proving the error bound uniformly. Partitions of arbitrarily small diameter exist by compactness. For the last assertion, the bounded-density responses are exactly fixed by the additive identity and marginal expectations; pass to the limit. $\square$ [Checkerboard approximation of copulas](https://www.impan.pl/shop/publication/transaction/download/product/84518)

**Theorem 15 (an exponential density cost at any fixed interaction order).** Fix $k\ge2$ and take $m$ disjoint blocks of $k$ independent unbiased signs, with the product reference on $km$ coordinates. Observe every marginal on at most $k-1$ coordinates. Let $Y_j$ be the parity product in block $j$, and put $g=m^{-1}\sum_jY_j$. The global upper expectation over compatible laws is $1$, and reaching it requires density cap at least $2^m$ relative to the reference. Under any density cap $B\ge1$,
$$
 \mathbb E_\mu g\le\sqrt{2\log B/m}.
\tag{10}
$$
Thus attaining even half the global value requires $B\ge e^{m/8}$. This holds for a response of interaction order $k$, with all its local tested marginals independent.

*Proof.* Condition each block independently on parity $+1$. Within a parity class any proper subset of its bits is uniform, so this joint law has the stipulated observations. It has $g=1$ almost surely; any law attaining 1 is supported on the event of reference probability $2^{-m}$ that all parities are $+1$. The conditional law on that event attains the cap $2^m$.

If the density is bounded by $B$, its relative entropy is at most $\log B$. For $t>0$, nonnegativity of relative entropy with respect to the exponentially tilted reference gives $t\,\mathbb E_\mu g\le \log B+\log\mathbb E_\lambda e^{tg}$. Under the reference the parities are independent signs and this last log is $m\log\cosh(t/m)\le t^2/(2m)$. Optimize over $t$ and use continuity at $B=1$. $\square$

More precisely, any law on the parity vector can be lifted by using the reference conditional law within each parity class. This keeps all the observed marginals, and the density cap is exactly the cap on the parity distribution against the uniform parity vector. The support problem is therefore a finite sorting problem: assign as much mass as permitted to the parity values of largest $g$, with a partial allowance on the last level. This monotone rearrangement gives the exact curve for every $B$, and (10) displays its dimension dependence in a simple form.

## 7. A joint geometry that finite classical models cannot reproduce

**Proposition 16.** Work at a maximally mixed quantum reference, and let $A$ be the observed span. Suppose $P_1,\ldots,P_\ell$ are Hermitian matrices with $P_i^2=I$, that distinct ones anticommute, and that all $P_i$ are trace-orthogonal to $A$. Their joint centered attainable region at radius $r$ is the Euclidean ball of radius $r$ in $\mathbb R^\ell$. For $\ell\ge2$ and $r>0$, no finite classical affine model with box-bounded densities and linear observations can give the same entire region.

*Proof.* For $G=\sum_i c_iP_i$, anticommutation gives $G^2=\|c\|_2^2I$. Thus (4) with the zero candidate gives support at most $r\|c\|_2$. For $c\ne0$ take $H=r G/\|c\|_2$, which is in the admissible annihilator and attains the bound. The support function identifies the ball. In a finite classical model the feasible set of density perturbations is cut out by finitely many linear constraints and coordinate bounds. It is a polytope, as is any linear response image; a positive-radius Euclidean ball of dimension at least two has infinitely many extreme points. $\square$ [Joint numerical ranges of Pauli strings](https://arxiv.org/abs/2308.00753)

For example, $X\otimes X$ and $Z\otimes X$ on two qubits anticommute and have zero partial trace to either qubit. Observing both single-qubit states fixes neither joint expectation. Their exact two-dimensional response region is a disk, while each individual interval is $[-r,r]$. The discrepancy only appears when both responses are asked for jointly.


**Proposition 17 (finite approximate recoding of the ball).** For dimension $\ell$ and $0<\epsilon<1/2$, a finite classical model with $O(\ell\epsilon^{-2}\log(2/\epsilon))$ atoms can approximate the ball in Proposition 16 within relative Hausdorff error $\epsilon$ at every radius $r$. The same atom model works for all $r$. At fixed error the linear order in $\ell$ is necessary.

*Proof.* Let $w_1,\ldots,w_m$ be independent standard Gaussian vectors in $\mathbb R^\ell$. Use $2m$ equiprobable atoms $(i,\sigma)$, $\sigma=\pm1$, observe only normalization, and set the response at this atom to $\sigma w_i/\sqrt{2/\pi}$. The support function at radius $r$ in direction $c$ is
$$
 \frac{r}{m\sqrt{2/\pi}}\sum_{i=1}^m |c\cdot w_i|.
$$
The maximizer has opposite perturbation signs at each pair of atoms, so it satisfies normalization. For any fixed unit $c$ the normalized sum has mean one. For $Z$ standard normal and $W=|Z|-\sqrt{2/\pi}$, the inequality $e^{tW}\le1+tW+\tfrac12t^2 W^2 e^{|W|}$ for $|t|\le 1$ gives $\mathbb E e^{tW}\le e^{Ct^2}$, with an absolute finite $C$. Applying Markov to both tails yields probability at most $2e^{-c_0m\epsilon^2}$ for a fixed small relative error, with absolute positive $c_0$.

Use a Euclidean net of mesh $\epsilon/8$ on the unit sphere of cardinality at most $(1+16/\epsilon)^\ell$, by the volume bound for disjoint balls. The union bound at tolerance $\epsilon/4$ gives an outcome good on the net with the claimed $m$. If $T$ denotes the normalized empirical support at $r=1$, its maximum on the unit sphere is at most $\max_{\rm net}T/(1-\epsilon/8)$, by subadditivity. The same inequality with the closest net point bounds $T$ below throughout the sphere by $\min_{\rm net}T-(\epsilon/8)\max T$. Together these give $|T(c)-1|\le\epsilon$ for each unit $c$. Uniform control of support functions on the unit sphere is exactly Hausdorff control for compact convex sets, by separation. Scaling gives all radii. Finally, a classical model with $a$ atoms has centered response image of affine dimension at most $a-1$. A body of dimension less than $\ell$ cannot approximate the unit ball at Hausdorff distance less than one. $\square$

The remaining approximation question is for a general observed quantum response body (4). At fixed relative error and after an affine normalization to a centrally symmetric body, does a polynomial number of classical atoms in the response dimension and the matrix dimension always suffice when arbitrary linear probes are allowed? The random sign-pair construction above establishes this only for the Euclidean ball.
