# A CLIQUE Reduction for Symmetric Tensor Positivity with Every Paired-Index Entry Fixed to One

**Date:** November 10, 2026

**Proof status:** A self-contained informal proof, with exact rational thresholds. Not peer-reviewed; priority and potential later literature solutions are not definitively settled.

**Claim proved here:** For rational, fully symmetric order-four tensors whose entries with four indices of even multiplicity are all **1**, non-positive-semidefiniteness is NP-hard and positive-semidefiniteness is coNP-hard.

**Not claimed:** NP-hardness of membership in the separate Carathéodory tensor cone, nor hardness of the entire constrained optimization program with its additional affine condition.

## 1. The published open problem

Chuyang Ke and Jean Honorio, *Exact Partitioning of High-order Models with a Novel Convex Tensor Cone Relaxation*, **Journal of Machine Learning Research** 23(284):1–28 (2022), §4 and Appendix C (p. 22), explicitly state that the ordinary hardness reduction for positive semidefiniteness of symmetric tensors does not survive their normalization constraint. In their notation, for a fully symmetric even-order tensor S, all entries whose index multiset can be partitioned into equal-index pairs are fixed at 1:

\[
S_{\sigma(i,i,j,j)}=1 \quad (\text{all }i,j\text{ and permutations }\sigma)
\]

for order 4 (including \(S_{iiii}=1\)). They identify the complexity of positivity testing under this restriction as open. Their source also poses a distinct question about membership in the Carathéodory symmetric tensor cone, which is **not** addressed here.

Source: https://jmlr.org/papers/v23/22-0232.html ; PDF: https://jmlr.org/papers/volume23/22-0232/22-0232.pdf (Appendix C, p. 22).

### Theorem (restricted quartic PSD hardness)

There is a polynomial-time map that sends a graph \(G\) on \(n\) vertices and an integer \(3\le k\le n\) to a **fully symmetric rational fourth-order tensor** \(T=T(G,k)\) of dimension \(D=8n^3\), such that:

1. \(T_{abcd}=1\) whenever every index in the multiset \(\{a,b,c,d\}\) occurs an even number of times;
2. \(G\) has no clique of size \(k\) if and only if \(T\) is positive semidefinite;
3. in fact, when \(G\) has no \(k\)-clique, \(T\) is **positive definite**; when \(G\) has a \(k\)-clique, an explicit nonzero rational vector \(X\) has \(\langle T,X^{\otimes4}\rangle<0\).

Consequently, detecting a negative direction under the paired-entry normalization is NP-hard under polynomial-time many-one reductions. Equivalently, the **PSD membership problem is coNP-hard**. A polynomial-time algorithm for membership would imply \(P=NP\). The reduction does **not** establish coNP membership or a complexity-class completeness result.

## 2. The universal convex baseline

For \(X=(X_1,\dots,X_D)\in\mathbb R^D\) define

\[
B_D(X)=\sum_{a=1}^D X_a^4+6\sum_{1\le a<b\le D}X_a^2 X_b^2
       =3\|X\|_2^4-2\sum_a X_a^4.
\]

This polynomial is the form of the unique fully symmetric order-four tensor that has entry **1** on all even-multiplicity index quadruples and entry **0** elsewhere. Indeed, each monomial \(X_a^2X_b^2\) with \(a\ne b\) occurs in the full tensor contraction with multiplicity \(4!/(2!2!)=6\).

**Lemma 1 (convexity).** \(B_D\) is convex on all of \(\mathbb R^D\), not merely on the nonnegative orthant.

**Proof.** For any \(X,Z\in\mathbb R^D\), direct differentiation and regrouping give the exact sum-of-squares Hessian identity

\[
Z^\mathsf T\nabla^2 B_D(X)Z
=12\left[(X\cdot Z)^2+
\sum_{a<b}(X_a Z_b+X_b Z_a)^2\right]\ge0.
\]

Thus the Hessian is positive semidefinite at every point. QED.

## 3. Encode an arbitrary graph using only unconstrained tensor entries

Let \(G=([n],E)\). Choose an integer cloning parameter

\[
q=4n^2,\qquad D=2nq=8n^3.
\]

Use \(2n\) groups of \(q\) variables:

\[
\{X^U_{i,r}:1\le i\le n,1\le r\le q\},\quad
\{X^V_{i,r}:1\le i\le n,1\le r\le q\}.
\]

For each vertex define the rational group means

\[
a_i=\frac1q\sum_{r=1}^{q}X^U_{i,r},\qquad
b_i=\frac1q\sum_{r=1}^{q}X^V_{i,r}.
\]

Define the graph quartic

\[
h_G(a,b)=\sum_{\{i,j\}\in E}a_i b_i a_j b_j.
\]

If \(i\ne j\), then every summand, expanded in the original \(X\) coordinates, is a product of **four distinct variables**: one each from \(U_i,V_i,U_j,V_j\). Thus changing the coefficient of \(h_G\) changes **no** prescribed even-multiplicity tensor entry.

For each integer \(t\ge2\), put

\[
H_t=\frac{t-1}{8t}.
\]

For the input CLIQUE threshold \(k\ge3\), set

\[
H_-=H_{k-1},\qquad H_+=H_k,\qquad
H_*=\frac{H_-+H_+}{2},\qquad
\lambda=\frac3{H_*}.
\]

All constants are rational with polynomially many bits. Construct the homogeneous quartic

\[
\boxed{P_{G,k}(X)=B_D(X)-\lambda q^2 h_G(a(X),b(X)).}
\]

Let \(T(G,k)\) be its unique fully symmetric coefficient tensor:
\(P_{G,k}(X)=\langle T(G,k),X^{\otimes4}\rangle\).

The graph term has no monomial with a repeated original coordinate index, so every entry of \(T\) whose index multiset is \((a,a,b,b)\) or \((a,a,a,a)\) remains **exactly 1**. More explicitly, for a graph-edge pattern of four distinct original indices, each of its \(4!\) symmetric tensor entries equals \(-\lambda/(24q^2)\); other all-distinct entries are zero. The output has dimension \(8n^3\) and at most \(D^4=O(n^{12})\) entries, so its explicit rational encoding is polynomial-time constructible.

## 4. Clone averaging does not weaken positivity testing

Let \(\bar X\) replace every one of the \(q\) coordinates in each group by that group's arithmetic mean. Then \(a(\bar X)=a(X)\), \(b(\bar X)=b(X)\) and hence \(h_G\) is unchanged.

The vector \(\bar X\) is the average of all vectors obtained from \(X\) by independently permuting clones within each group. Since \(B_D\) is convex and invariant under these permutations, Jensen's inequality gives

\[
B_D(\bar X)\le B_D(X),\qquad
P_{G,k}(\bar X)\le P_{G,k}(X).
\]

It follows that **\(P_{G,k}\ge0\) on every real \(X\) if and only if it is nonnegative on vectors constant within each clone group.**

Let \(y=(a_1,\ldots,a_n,b_1,\ldots,b_n)\). For the clone-constant vector,

\[
\|\bar X\|_2^2=q\|y\|_2^2,\qquad
\sum_{r=1}^{D}\bar X_r^4=q\sum_{i=1}^n(a_i^4+b_i^4).
\]

Therefore

\[
\boxed{P_{G,k}(\bar X)=q^2\left[
  3\|y\|_2^4-\frac2q\sum_i(a_i^4+b_i^4)-\lambda h_G(a,b)
\right].}\tag{1}
\]

Since \(\sum_i(a_i^4+b_i^4)\le\|y\|_2^4\), the fixed-entry baseline differs from the radial polynomial \(3\|y\|_2^4\) by at most \((2/q)\|y\|_2^4\). The cloning is what makes this error small without changing any mandated tensor entry.

## 5. The exact graph maximum (Motzkin–Straus)

Write \(\omega=\omega(G)\) for the clique number. We claim

\[
\boxed{\max_{\|y\|_2=1} h_G(a,b)=H_\omega=\frac{\omega-1}{8\omega}.}\tag{2}
\]

**Proof.** Put \(w_i=|a_i b_i|\). By \(2|a_ib_i|\le a_i^2+b_i^2\),

\[
s:=\sum_i w_i\le\frac{\|a\|_2^2+\|b\|_2^2}{2}=\frac12.
\]

Because graph-edge coefficients are nonnegative,

\[
h_G(a,b)\le\sum_{\{i,j\}\in E}w_iw_j.
\]

For nonnegative weights \(z_i\) summing to 1, the Motzkin–Straus identity gives

\[
\max_{z\ge0,\ \sum z_i=1}\sum_{\{i,j\}\in E}z_iz_j
=\frac12\left(1-\frac1\omega\right).
\]

For completeness, this identity has an elementary proof: if a maximizer gives positive weight to nonadjacent vertices \(i,j\), transferring all their combined weight to whichever has the larger weighted neighbor sum does not decrease the objective. Repeating leaves support on a clique of size \(r\le\omega\). On that clique the objective is \(\frac12(1-\sum z_i^2)\le\frac12(1-1/r)\le\frac12(1-1/\omega)\). Uniform weights on a maximum clique achieve equality.

Scaling the identity by \(s^2\) yields

\[
h_G(a,b)\le\frac14\cdot\frac12\left(1-\frac1\omega\right)=H_\omega.
\]

Equality is achieved by taking \(a_i=b_i=1/\sqrt{2\omega}\) on a maximum clique, zero elsewhere. This vector has norm 1. QED.

Homogeneity implies for every real \(y\),

\[
h_G(y)\le H_{\omega(G)}\|y\|_2^4.\tag{3}
\]

## 6. Exact rational separation of the two CLIQUE cases

The two relevant maxima are

\[
H_- =\frac{k-2}{8(k-1)},\qquad
H_+=\frac{k-1}{8k},\qquad
H_+-H_- = \frac1{8k(k-1)}>0.
\]

We chose \(\lambda=3/H_*\) with \(H_*=(H_-+H_+)/2\), so

\[
\lambda H_+>3.
\]

On the other side,

\[
3-\lambda H_-=
\frac{3(H_+-H_-)}{2H_*}
\ge\frac{3(H_+-H_-)}{2H_+}
=\frac{3}{2(k-1)^2}
\ge\frac{3}{2n^2}
>\frac{1}{2n^2}=\frac2q.
\]

Thus, with strictly positive rational margin,

\[
\boxed{3-\frac2q-\lambda H_->0,\qquad 3-\lambda H_+<0.}\tag{4}
\]

**No-case: \(\omega(G)\le k-1\).** Use (3), the quartic norm bound, (1) and (4):

\[
P_{G,k}(\bar X)
\ge q^2\left(3-\frac2q-\lambda H_-\right)\|y\|_2^4\ge0.
\]

Since \(P(X)\ge P(\bar X)\), the tensor is PSD. Indeed it is positive definite: if \(y\ne0\), the displayed lower bound is strict; if \(y=0\) and \(X\ne0\), then \(h_G=0\) and \(P(X)=B_D(X)>0\).

**Yes-case: \(\omega(G)\ge k\).** Select any clique \(C\subseteq[n]\) of size \(k\), and choose an **integer** vector \(X\): set every clone in \(U_i,V_i\) to 1 for \(i\in C\), and every other clone to 0. Its mean vector satisfies \(a_i=b_i=1\) on \(C\) and zero otherwise. Let \(y=(a,b)\). Then \(\|y\|_2^2=2k\), and the normalized quartic graph value is \(h_G(y)/\|y\|_2^4=H_k=H_+\). By (1),

\[
\begin{aligned}
P_{G,k}(X)
&=q^2\left[3(2k)^2-\frac{2}{q}(2k)-\lambda {k\choose 2}\right]\\
&=4k^2q^2\left[3-\frac{1}{kq}-\lambda H_+\right]
<0,
\end{aligned}
\]

because \(\lambda H_+>3\). This is an explicit integer-valued negative direction. Therefore the tensor is **not** PSD.

The equivalence and polynomial-time many-one reduction are proved. QED.

## 7. Small exact check

For a graph with \(n=3\), asking whether it has a triangle (\(k=3\)):

\[
q=36,\qquad D=216,\qquad H_2=\frac1{16},\quad
H_3=\frac1{12},\quad H_*=\frac7{96},\quad
\lambda=\frac{288}{7}.
\]

The no-triangle positivity margin in (4) is

\[
3-\frac{2}{36}-\frac{288}{7}\cdot\frac1{16}
=\frac{47}{126}>0.
\]

For the triangle, the all-one-on-clique integer witness has \(2kq=216\) nonzero entries. The baseline equals \(B_D(X)=139536\), the graph quartic is \(h_G=3\), and

\[
P_{G,3}(X)=139536-\frac{288}{7}(36)^2(3)
=-\frac{142992}{7}<0.
\]

All calculations use exact integers and rational numbers.

## 8. Scope, limitations and why the reduction bridges toward tensors

- **Proved:** The fixed paired-index normalization does *not* make fully symmetric quartic PSD testing tractable in general. Even with every prescribed entry exactly 1, recognizing a negative real direction is NP-hard, and recognizing PSD is coNP-hard.
- **Proved:** The no-clique instances are strictly positive definite; the clique instances admit explicit integer negative witnesses.
- **Not proved:** Hardness of membership in the *Carathéodory* symmetric tensor cone (a separate question in the same paper); hardness of the whole optimization program (3) including its distinct affine equation \(\langle Y,\mathbf1^{\otimes4}\rangle=0\); hardness for every even order individually; or any result about tensor isomorphism (TI), TI_SL, VP, or VNP.
- **Source status:** A targeted literature search in November 2026 did not locate a later resolution of this exact fixed-paired-entry hardness question. That is not a complete novelty audit and no priority claim is made.

The reusable architecture is *finite-to-global positivity transfer*: an exact graph witness is embedded entirely in unconstrained tensor coefficients, while a convex positive baseline enforces mandatory coefficients and Jensen clone averaging reduces an arbitrarily large tensor's positivity to an exact low-dimensional inequality. The proof uses simultaneous positive and negative certificates with an explicit rational gap. Those are concrete tools for later tensor-reduction and orbit-hardness work; the present theorem is **not** itself a tensor-isomorphism hardness theorem.

## References

1. Chuyang Ke and Jean Honorio, *Exact Partitioning of High-order Models with a Novel Convex Tensor Cone Relaxation*, **JMLR** 23(284):1–28 (2022), §4, Appendix C, p. 22. https://jmlr.org/papers/v23/22-0232.html ; https://jmlr.org/papers/volume23/22-0232/22-0232.pdf
2. L. Motzkin and E. Straus, *Maxima for Graphs and a New Proof of a Theorem of Turán*, Canadian Journal of Mathematics **17** (1965), 533–540. https://doi.org/10.4153/CJM-1965-053-6
3. Christopher J. Hillar and Lek-Heng Lim, *Most Tensor Problems Are NP-Hard*, **Journal of the ACM** 60(6), article 45 (2013). https://doi.org/10.1145/2512329
4. Yang–Mills group, *OpenAI-YM-20261028*, https://github.com/yang-mills-group/OpenAI-YM-20261028 — conceptual inspiration for certificate discipline and positivity-preserving finite constructions, **not** a logical dependency of this theorem.
