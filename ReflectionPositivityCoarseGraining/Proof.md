# A finite-dimensional counterexample to reflection positivity under CP coarse-graining

**Date:** 10 November 2026

**Status:** Complete elementary solution of the **specific yes/no implication** in the unanswered MathOverflow question of 15 November 2025, plus an exact classification of a symmetric two-spin family. This is an independent mathematical result, **not** a new proof of the Yang–Mills existence theorem or of a mass gap. It has not undergone peer review.

**Literature problem:** [When do θ-commuting CP maps preserve the Osterwalder–Schrader reflection positivity cone?](https://mathoverflow.net/questions/503899/when-do-%CE%B8-commuting-cp-maps-preserve-the-osterwalder-schrader-reflection-positiv) (Giedrius K, 15 Nov 2025; no posted answer at time of checking).

**Related problem:** [CP RG maps and preservation of Osterwalder–Schrader reflection positivity](https://mathoverflow.net/questions/504120/cp-rg-maps-and-preservation-of-osterwalder-schrader-reflection-positivity) (20 Nov 2025).

**Technique source:** [OpenAI-YM-20261028](https://github.com/yang-mills-group/OpenAI-YM-20261028), especially `PublicWilson.lean` (finite normalized positive integration), the same-hierarchy requirement, and the compact-limit positivity/reconstruction strategy described in its README.

## 1. The genuinely separate question

The posted problem asks whether the following conditions suffice for a renormalization/coarse-graining map `K` to preserve Osterwalder–Schrader reflection positivity:

1. `K` is completely positive (CP) and unital;
2. `K` carries the algebra of observables on one side of a reflection into itself;
3. `K` commutes with reflection (at least on that one-sided algebra).

**Answer: No.** There is a counterexample on **two binary spins**, with all spaces finite-dimensional. Not only can `K` fail to preserve the reflection-positive cone, but it can transform an actual reflection-positive probability state into a non-reflection-positive probability state. Even full support and strict positivity of the transition probabilities do not prevent failure.

A second question asks what structural hypothesis *does* suffice, and whether all such maps must be conditional expectations. We provide a broad class of **synchronized mirror-product channels** that work, including non-idempotent maps, and then completely classify a natural three-parameter two-spin family.

### Convention caveat

For a complex `*`-algebra, the standard mirror square is `θ(f)^* f`, with `θ` a complex-linear reflection `*`-automorphism. The question's displayed cone uses `(θZ)Z` without an explicit `*`; this must be understood as using an **antilinear** `θ`, or as shorthand for the standard form. Literally using a complex-linear reflection with no star makes the cone contain both `1` and `-1` (take `Z=1` and `Z=i`), so **no** state would be nonnegative on it. All counterexamples below already use **real-valued** `f`, so this convention does not change the negative conclusion.

## 2. Exact finite setting: mirror squares are positive semidefinite matrices

Let `X={0,1}` and

\[
 A=C(X\times X;\mathbb C)\cong\mathbb C^4.
\]

Interpret the first spin `x` as the left site and the second `y` as its reflected right site. Let

\[
 (\theta F)(x,y)=F(y,x),\qquad
 A_L=\{F(x,y)=f(x):f\in C(X;\mathbb C)\}.
\]

For `f` regarded as a left observable, its standard mirror square is

\[
 S_f(x,y)=(\theta f)^*(x,y)\,f(x,y)
       =\overline{f(y)}f(x).
\]

Under the identification `F` ↔ its `2×2` matrix `[F(x,y)]`, `S_f=ff^*` is rank-one Hermitian positive semidefinite (PSD). Since every PSD matrix is a finite sum of rank-one PSD matrices, the closed OS cone is **exactly**

\[
 C_{\rm RP}=\{F\in A:[F(x,y)]_{x,y\in X}\succeq0\}.
\tag{1}
\]

Here `F\succeq0` is **matrix** positivity, *not* pointwise nonnegativity as a function on `X×X`.

A state on `A` is a probability table

\[
 \varphi(F)=\sum_{x,y}w_{xy}F(x,y),\quad
 w_{xy}\ge0,\quad \sum_{x,y}w_{xy}=1.
\]

It is reflection-positive precisely when the table `W=[w_xy]` is PSD: testing `\varphi(S_f)` for all `f` is equivalent to `f^*Wf\ge0` (up to harmless transposition/conjugation). This characterization includes symmetry of `W`, forced by the requirement that all such quadratic forms be real and nonnegative.

## 3. The counterexample: a stochastic map that destroys OS positivity

Order the four configurations as

\[
 00,\quad 01,\quad 10,\quad 11.
\]

Define a linear map `K:A→A` by the following `4×4` stochastic transition matrix (rows = input `(x,y)`, columns = sampled output `(a,b)`):

\[
 T=\begin{pmatrix}
 0&\tfrac12&\tfrac12&0\\
 \tfrac12&0&0&\tfrac12\\
 \tfrac12&0&0&\tfrac12\\
 0&\tfrac12&\tfrac12&0
 \end{pmatrix},
 \qquad
 (KF)(x,y)=\sum_{a,b}T_{xy}^{ab}F(a,b).
\tag{2}
\]

In words: when the two input spins **agree**, the map samples two **opposite** output spins; when the input spins **disagree**, it samples two **equal** output spins. In either case the two allowed outputs occur with probability `1/2` each.

### Theorem 1 (negative answer to the posted problem)

The map `K` defined in (2) satisfies all three advertised properties—unital complete positivity, preservation of `A_L`, and commutation with `θ` on **all** of `A`—but

\[
 K(C_{\rm RP})\not\subseteq C_{\rm RP}.
\]

Moreover, a reflection-positive state `\varphi` exists for which `\varphi\circ K` is not reflection-positive.

### Proof

**Step 1: unital complete positivity.** Each row of `T` is a probability distribution, so `K1=1`. More strongly, `K` is a positive Markov operator on a commutative finite-dimensional C*-algebra, and hence is CP. Explicitly, if `[F_ij]` is pointwise a PSD matrix of functions, then at each input `(x,y)` the block matrix `[KF_ij(x,y)]` is a convex combination of PSD matrices `[F_ij(a,b)]`, and is therefore PSD. This proves complete positivity at every matrix level.

**Step 2: one-side preservation.** For every left observable `f(a)`, the output left marginal is fair, independent of both input spins:

\[
 K(f\otimes1)(x,y)=\tfrac12(f(0)+f(1)).
\]

The result is constant, and therefore lies in `A_L`. Hence `K(A_L)\subseteq A_L`.

**Step 3: full reflection commutation.** The transition probabilities satisfy

\[
 T_{yx}^{ba}=T_{xy}^{ab}
\]

for all four input and output configurations. Thus `K(\theta F)=\theta(KF)` for **every** `F`, a stronger property than requested.

**Step 4: explicit failed mirror square.** Define the real left observable

\[
 u(0)=1,\qquad u(1)=-1.
\]

Its mirror square is the PSD kernel

\[
 S_u(x,y)=u(x)u(y),\qquad
 [S_u]=\begin{pmatrix}1&-1\\-1&1\end{pmatrix}\succeq0.
\]

Applying (2) yields

\[
 [KS_u]=\begin{pmatrix}-1&1\\1&-1\end{pmatrix}.
\]

This matrix has eigenvalues `0` and `-2`; in particular its `00` diagonal entry is `-1`. Every matrix in `C_RP` has nonnegative diagonal entries. Thus `KS_u` **does not belong** to `C_RP`.

**Step 5: an actual RP state becomes non-RP.** Take the state `\varphi(F)=F(0,0)`, i.e. the point mass on the `00` configuration. It is reflection-positive, since

\[
 \varphi(S_f)=|f(0)|^2\ge0
\]

for every left `f`. But

\[
 (\varphi\circ K)(S_u)=(KS_u)(0,0)=-1<0.
\]

Hence the pushed-forward state is not RP. **QED.**

### Robustness: no zero transition probabilities or singular initial state are needed

Let `J_4` be the `4×4` all-ones matrix and set

\[
 T_{\rm strict}=\tfrac12 T+\tfrac18J_4
 =\begin{pmatrix}
 \tfrac18&\tfrac38&\tfrac38&\tfrac18\\
 \tfrac38&\tfrac18&\tfrac18&\tfrac38\\
 \tfrac38&\tfrac18&\tfrac18&\tfrac38\\
 \tfrac18&\tfrac38&\tfrac38&\tfrac18
 \end{pmatrix}.
\tag{3}
\]

All sixteen transition probabilities are **strictly positive**. The same structural properties hold. Choose the **full-support** initial probability table

\[
 W=\frac18\begin{pmatrix}3&1\\1&3\end{pmatrix},
\]

which is positive definite (eigenvalues `1/2` and `1/4`) and thus RP. The image table under (3) is

\[
 W'=\frac1{16}\begin{pmatrix}3&5\\5&3\end{pmatrix},
\]

whose eigenvalues are `1/2` and `-1/8`. Equivalently,

\[
 (\varphi_W\circ K_{\rm strict})(S_u)=-\frac14.
\]

So both the initial state and the transition mechanism may have **full support**, with all probabilities strictly positive, while OS reflection positivity still fails. This failure is not a boundary or zero-probability artifact.

## 4. An effective sufficient condition: synchronize the two reflected channels

### Theorem 2 (mirror-synchronized Markov criterion)

Let `X` be **any** finite set. Choose stochastic matrices `P_α` on `X` and probabilities `p_α≥0` summing to one. Define

\[
 (K_PF)(x,y)
 =\sum_\alpha p_\alpha
    \sum_{a,b\in X}P_\alpha(x,a)P_\alpha(y,b)F(a,b).
\tag{4}
\]

Then `K_P` is unital CP, preserves the left algebra, commutes with reflection, **and preserves the entire RP cone**.

### Proof

As in Theorem 1, (4) is a stochastic kernel and hence a unital CP map on `C(X×X)`. The left output marginal is `\sum_\alpha p_\alpha P_\alpha(x,a)`, independent of the right input `y`, and the expression is symmetric under simultaneous exchange `x↔y` and `a↔b`.

The decisive extra property is that, when matrices represent two-sided functions, we have the exact identity

\[
 [K_PF]=\sum_\alpha p_\alpha\,P_\alpha[F]P_\alpha^{\mathsf T}.
\tag{5}
\]

For every PSD matrix `[F]`, each congruence `P_α[F]P_α^T` is PSD. Their nonnegative combination is PSD. Equation (1) proves cone preservation. **QED.**

The point is **not** just that the two marginal channels are equal; their **joint** behavior must admit the synchronized decomposition (4). The counterexample has equal fair marginals but has negative correlations between its reflected outputs.

### These channels are not restricted to conditional expectations

Take the stochastic matrix

\[
 P=\begin{pmatrix}3/4&1/4\\1/4&3/4\end{pmatrix}
\]

and define `K_P` using a single term in (4). Since `Pu=(1/2)u`,

\[
 K_P(S_u)=\frac14 S_u,
 \qquad
 K_P^2(S_u)=\frac1{16}S_u\ne K_P(S_u).
\]

Thus `K_P^2\ne K_P`. It is **not** a conditional expectation (which must be idempotent), yet it preserves RP. Any finite composition of maps from Theorem 2 is also RP-cone-preserving, even if the composite does not come in the same mixture form.

## 5. Complete solution of a symmetric two-spin family

The previous theorems establish a negative answer and a broad positive class. We can go further and classify an entire three-parameter family, including an important distinction between **preserving the cone** and **preserving every RP probability state**.

Assume `X={0,1}`, and require the output marginals on each side to be uniform. Every mirror-symmetric coupling of two uniform binary marginals has probabilities

\[
 T_{xy}^{00}=T_{xy}^{11}=q_{xy},\qquad
 T_{xy}^{01}=T_{xy}^{10}=\tfrac12-q_{xy},
 \qquad 0\le q_{xy}\le\tfrac12,
 \quad q_{01}=q_{10}.
\tag{6}
\]

Write

\[
 C=[c_{xy}],\qquad c_{xy}=4q_{xy}-1,
 \quad e=(1,1)^{\mathsf T},\quad u=(1,-1)^{\mathsf T}.
\]

For **any** Hermitian PSD input kernel `F`, direct expansion of (6) gives

\[
 K(F)=\alpha\,ee^{\mathsf T}+\delta\,C,
\qquad
\alpha=\tfrac14e^*Fe\ge0,
\quad\delta=\tfrac14u^*Fu\ge0.
\tag{7}
\]

Conversely, `F=uu^T` gives `α=0` and `δ=1`.

### Theorem 3 (exact cone-preservation criterion)

For the entire family (6), the following conditions are equivalent:

- `K(C_RP)⊆C_RP`;
- `C=[4q_xy−1]` is PSD;
- with `a=4q_00−1`, `b=4q_01−1`, and `d=4q_11−1`,

\[
 \boxed{a\ge0,\qquad d\ge0,\qquad b^2\le ad.}
\tag{8}
\]

**Proof.** If `C` is PSD, (7) is a nonnegative sum of PSD matrices. Conversely, apply `K` to the mirror square `uu^T`; its image is `C` itself, so cone preservation forces `C` to be PSD. For a symmetric real `2×2` matrix, PSD is exactly (8). **QED.**

### Theorem 4 (exact preservation-of-states criterion)

For the same family (6), **every** reflection-positive probability state `φ` remains RP under `φ∘K` if and only if `C` is **copositive** (i.e. `v^T C v≥0` for every real `v` whose two coordinates are nonnegative). In dimension two, this is exactly

\[
 \boxed{a\ge0,\qquad d\ge0,\qquad b\ge-\sqrt{ad}.}
\tag{9}
\]

This is **strictly weaker** than cone preservation (8).

**Proof.** An RP state has a matrix `W=[w_xy]` that is both PSD and entrywise nonnegative. Pairing (7) with its probability table yields

\[
 (\varphi_W\circ K)(F)
 =\alpha+\delta\sum_{x,y}w_{xy}c_{xy}.
\tag{10}
\]

Thus it remains RP for all input mirror squares precisely when `⟨W,C⟩≥0` for every entrywise-nonnegative PSD `W`. Every such real `2×2` matrix is a sum of matrices `vv^T` with `v≥0`: if
`W=[[s,t],[t,r]]`, `s>0`, use

\[
 W=\binom{\sqrt{s}}{t/\sqrt{s}}
    (\sqrt{s},t/\sqrt{s})
   +\begin{pmatrix}0&0\\0&r-t^2/s\end{pmatrix},
\]

and the case `s=0` is diagonal. Conversely, each `vv^T` with `v≥0` normalizes to an RP probability table. Consequently (10) is nonnegative for all RP states if and only if `v^TCv≥0` for every `v≥0`, i.e. copositivity. The elementary quadratic-form condition for a `2×2` real symmetric matrix is (9). **QED.**

### A surprising strict separation: state preservation without cone preservation

Let `q_00=q_11=1/4` and `q_01=q_10=3/8`. Then

\[
 C=\begin{pmatrix}0&1/2\\1/2&0\end{pmatrix}.
\]

This is **not PSD** (one eigenvalue is `−1/2`), so the map does **not** preserve `C_RP`. However, `v^TCv=v_0v_1≥0` for every nonnegative `v`, so it satisfies (9) and **does preserve every RP probability state**.

Therefore the implications are genuinely different:

\[
 \boxed{\text{RP-cone preservation}\ \Longrightarrow\
 \text{preservation of all RP states}}
\]

but the converse fails, even within the highly symmetric fair-marginal class. This subtlety is relevant when choosing which precise property an RG theorem actually needs.

## 6. Transfer from the Yang–Mills repository

The proof does **not** import `jointExistence`, any claimed asymptotic, or the Yang–Mills mass-gap problem. Its transferable elements are structural:

1. **Finite-regulator-first positivity.** `PublicWilson.lean` defines finite Wilson moments by a normalized positive integration law. We likewise begin with a finite positive stochastic kernel, checking CP exactly before taking any limit. The new point is that positivity *of the underlying probability law* does **not** imply OS *mirror* positivity.
2. **Use the same two-sided witness.** The repository emphasizes that its continuum field, OPE reader, and moment table belong to one selected hierarchy. Here the correct analogous constraint is that two reflected outputs be generated by the **same** stochastic channel realization, producing the exact congruence (5); merely matching their marginal distributions is not enough.
3. **Keep the invariant cone visible throughout blocking.** The correct finite-scale invariant is the positive-semidefinite **reflected Gram kernel**, not just complete positivity on the configuration algebra. Equation (5) is a checkable sufficient certificate.
4. **Stability through a consistent limit.** Any chain of cone-preserving maps preserves that cone. If a sequence of resulting reflected Gram matrices has an entrywise limit on each fixed finite test family, the limit is PSD because the finite-dimensional PSD cone is closed. For continuum QFT this alone is *not* sufficient: one also needs well-defined limiting distributions on all relevant tests, including control of coincident-point/contact terms, before asserting the full OS axioms. The repository treats such contact control as a distinct issue.

This is a **transfer of the finite-positive-witness, same-hierarchy, and closed-cone techniques**, not a claim that the repository already contains this counterexample or proves the required map criterion.

## 7. Exact checks, limitations and verdict

- The main `4×4` transition matrix has rational entries; every row sums to one.
- Its two output marginals are both uniformly `(1/2,1/2)` for every input.
- It is invariant under simultaneous exchange of the two input and two output spins.
- The single reflected-square test `S_u` has image with eigenvalues `0,-2`.
- The strictly positive perturbation has sixteen positive transition probabilities.
- A strictly RP, full-support input state `W=(1/8)[[3,1],[1,3]]` is mapped by that perturbation to `W'=(1/16)[[3,5],[5,3]]`, which has eigenvalues `1/2,-1/8`.
- The classification (8)–(9) is an **if and only if** result for the explicitly stated symmetric **uniform-marginal** family, not a classification of all infinite-dimensional quantum RG channels.
- No statement about a Wilson YM mass gap, preservation of every quantum OS axiom, or four-dimensional continuum gauge-theory RG is proved.

**Verdict.** The explicitly posted, previously unanswered **yes/no** question “Do unital CP, left-preserving, reflection-commuting maps necessarily preserve the OS reflection-positive cone?” is **disproved** by (2), and even its weaker “preserve RP states” variant is disproved. Equations (4)–(5) give nontrivial sufficient structural hypotheses that do not require conditional expectations. Equations (8)–(9) give an exact solution in the natural symmetric fair-binary family. This is a genuinely **separate** problem from the repository's Yang–Mills existence claim, with no dependence on the latter being correct.

## References

1. Giedrius K, *When do θ-commuting CP maps preserve the Osterwalder–Schrader reflection positivity cone?* MathOverflow, Nov 15, 2025: https://mathoverflow.net/questions/503899/when-do-%CE%B8-commuting-cp-maps-preserve-the-osterwalder-schrader-reflection-positiv
2. Giedrius K, *CP RG maps and preservation of Osterwalder–Schrader reflection positivity*, MathOverflow, Nov 20, 2025: https://mathoverflow.net/questions/504120/cp-rg-maps-and-preservation-of-osterwalder-schrader-reflection-positivity
3. Yang–Mills group, *OpenAI-YM-20261028*: https://github.com/yang-mills-group/OpenAI-YM-20261028
4. Finite Wilson integration formalization (`PublicWilson.lean`): https://github.com/yang-mills-group/OpenAI-YM-20261028/blob/main/PublicWilson.lean
5. The OS reflection-positivity framework: K. Osterwalder and R. Schrader, *Axioms for Euclidean Green's functions*, Communications in Mathematical Physics 31 (1973), 83–112; Part II, Communications in Mathematical Physics 42 (1975), 281–305.
