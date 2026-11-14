# Bivariate Polynomial Rank Separations via Squared Interpolation

**Status.** Informal proof, independently checked against the source definitions. Publication priority remains unverified.

This proves all three clauses of Conjecture 46 in *Polynomial decompositions with invariance and positivity inspired by tensors* by Gemma De las Cuevas, Andreas Klingler, and Tim Netzer, Linear Algebra and its Applications 698 (2024), 537–588. [Original paper](https://arxiv.org/abs/2109.06680)

For the single-edge decomposition structure `Lambda_1`, the authors' Conjecture 46 asserts there are no functions `f,g,h: N -> N` bounding, **uniformly over real bivariate polynomials of arbitrary degree**:

(i) `sep-rank(p) <= f(rank(p))` for separable `p`;

(ii) `sep-rank(p) <= g(sos-rank(p))` for separable `p`;

(iii) `sos-rank(p) <= h(rank(p))` for SOS `p`.

Here `rank` is the separation rank (sum of univariate products), `sep-rank` restricts local factors to sums of squares, and `sos-rank` is the minimum shared bond dimension in a family of sum-of-squares purifications as in Definition 31 of the source paper.

**Result.** All three clauses follow from a universal, exactly rank-preserving interpolation construction. The construction uses known nonnegative and PSD matrix rank separations.

## 1. The exact interpolation theorem

### Theorem

For any entrywise nonnegative real `m x n` matrix `M`, there exists a bivariate real polynomial `p_M(x,y)` satisfying **simultaneously**

\[
\boxed{\operatorname{rank}_{\Lambda_1}(p_M)=\operatorname{rank}(M),\quad
\operatorname{sep-rank}_{\Lambda_1}(p_M)=\operatorname{rank}_+(M),\quad
\operatorname{sos-rank}_{\Lambda_1}(p_M)=\operatorname{rank}_{\rm psd}(M).}
\]

Here `rank_+` is nonnegative matrix rank, and `rank_psd` is *real* positive semidefinite factorization rank. The local degrees of `p_M` are at most `2(m-1)` and `2(n-1)`.

### Construction

Choose distinct real nodes `a_1,...,a_m` and `b_1,...,b_n`. Let `L_i(x)` and `R_j(y)` be their Lagrange cardinal polynomials, so

\[
L_i(a_k)=\delta_{ik},\qquad R_j(b_l)=\delta_{jl}.
\]

Define

\[
\boxed{p_M(x,y)=\sum_{i=1}^{m}\sum_{j=1}^{n}M_{ij}L_i(x)^2R_j(y)^2.}\tag{1}
\]

This is manifestly separable over local SOS cones, and in particular SOS:

\[
p_M=\sum_{i,j}\left(\sqrt{M_{ij}}L_i(x)R_j(y)\right)^2.
\]

At the interpolation nodes, **exactly**

\[
p_M(a_i,b_j)=M_{ij}.\tag{2}
\]

### Ordinary rank: equality

A matrix factorization of rank `r` writes `M_ij=sum_{t=1}^r u_it v_jt`. Equation (1) becomes a sum of `r` univariate products

\[
p_M(x,y)=\sum_{t=1}^r\left(\sum_i u_{it}L_i(x)^2\right)
\left(\sum_j v_{jt}R_j(y)^2\right).
\]

So ordinary separation rank is at most `rank(M)`. Conversely any sum of `r` univariate products evaluates, via (2), to an ordinary rank-`r` factorization of `M`. Hence equality.

### Separable rank: equality

A nonnegative factorization `M_ij=sum_{t=1}^r u_it v_jt` with `u_it,v_jt>=0` yields the same decomposition above, but now each univariate factor is a *sum of squares* (a nonnegative sum of `L_i^2` or `R_j^2`). So `sep-rank(p_M)<=rank_+(M)`.

Conversely, for any decomposition `p_M=sum_{t=1}^r F_t(x)G_t(y)` with every `F_t,G_t` a univariate SOS, evaluation at the nodes yields

\[
M_{ij}=\sum_{t=1}^r F_t(a_i)G_t(b_j),\qquad F_t(a_i),G_t(b_j)\ge0.
\]

Therefore `rank_+(M)<=r`, proving equality.

### SOS-purification rank: equality

**Lower bound.** Suppose `p_M` has an SOS `Lambda_1`-decomposition of bond dimension `r`. By the definition of the paper, there are finite index sets `A,B` and functions `f_{a,t}(x),g_{b,t}(y)` such that

\[
p_M(x,y)=\sum_{a\in A,b\in B}q_{ab}(x,y)^2,\qquad
q_{ab}(x,y)=\sum_{t=1}^{r} f_{a,t}(x)g_{b,t}(y).
\]

For each node `a_i`, form the real PSD matrix

\[
U_i=\sum_{a\in A}f_a(a_i)f_a(a_i)^\top\in\mathbb S_+^r,
\qquad f_a=(f_{a,1},\ldots,f_{a,r})^\top,
\]

and similarly

\[
V_j=\sum_{b\in B}g_b(b_j)g_b(b_j)^\top\in\mathbb S_+^r.
\]

By expanding the squares,

\[
\operatorname{tr}(U_iV_j)
=\sum_{a,b}(f_a(a_i)^\top g_b(b_j))^2
=p_M(a_i,b_j)=M_{ij}.
\]

This is a PSD factorization of size `r`; therefore `rank_psd(M)<=sos-rank(p_M)`.

**Upper bound.** Conversely, let `M_ij=tr(U_i V_j)` be a real size-`r` PSD factorization. Choose rank-one expansions

\[
U_i=\sum_{a}u_{ia}u_{ia}^\top,\qquad
V_j=\sum_b v_{jb}v_{jb}^\top
\]

for `u_ia,v_jb in R^r`. Define the purification polynomials indexed by pairs `(i,a)` and `(j,b)`:

\[
q_{(i,a),(j,b)}(x,y)
=\sum_{t=1}^{r}\bigl((u_{ia})_t L_i(x)\bigr)
\bigl((v_{jb})_t R_j(y)\bigr).
\]

Every `q` has a shared bond decomposition of length at most `r`, and

\[
\sum_{i,a,j,b}q_{(i,a),(j,b)}(x,y)^2
=\sum_{i,j}\operatorname{tr}(U_iV_j)L_i(x)^2R_j(y)^2
=p_M(x,y).
\]

Thus `sos-rank(p_M)<=rank_psd(M)`. Equality follows.

**QED.** This is an exact identity for all three different rank notions, for every entrywise nonnegative matrix, using only two real polynomial variables.

## 2. Conjecture 46(i) and (ii): one explicit family

Let `M^(m)` be the `m x m` Euclidean squared-distance matrix

\[
M_{ij}^{(m)}=(i-j)^2,\qquad i,j\in\{1,\ldots,m\},\quad m\ge3.
\]

The three vectors with entries 1, i, and i² are linearly independent. The following factorization then gives ordinary rank exactly 3.

\[
(i-j)^2=i^2\cdot1+1\cdot j^2-2i\cdot j.
\]

It has a size-2 real PSD factorization:

\[
(i-j)^2=
\operatorname{tr}\left(
\begin{bmatrix}1&i\\i&i^2\end{bmatrix}
\begin{bmatrix}j^2&-j\\-j&1\end{bmatrix}
\right).
\]

Both matrices are rank-one PSD outer products, respectively of `(1,i)^T` and `(j,-1)^T`. Since matrix rank 3 precludes a size-1 PSD factorization, `rank_psd(M^(m))=2`.

The nonnegative rank diverges: `rank_+(M^(m))>=ceil(log_2(m))`. Here is an elementary proof. If `M=\sum_{t=1}^r u_t v_t^T` with nonnegative factors, the zero diagonal forces `u_t(i)v_t(i)=0` for every `i,t`. Let `S_i={t:u_t(i)>0}`. If two different indices had `S_i=S_j`, then `M_ij=0` because every `t` with `u_t(i)>0` also has `u_t(j)>0` and hence `v_t(j)=0`. But `M_ij>0` for `i!=j`. Thus all `S_i` are distinct subsets of `[r]`, giving `m<=2^r`.

Applying the exact interpolation theorem gives **separable bivariate polynomials** `p_m` with

\[
\boxed{\operatorname{rank}(p_m)=3,\quad
\operatorname{sos-rank}(p_m)=2,\quad
\operatorname{sep-rank}(p_m)\ge\lceil\log_2 m\rceil.}
\]

No uniform function of rank, nor of SOS rank, can bound separable rank. This proves Conjecture 46(i) and (ii).

## 3. Conjecture 46(iii): unbounded SOS rank at ordinary rank three

Take `M^(m)` instead to be the slack matrix of a **generic convex m-gon** in `R^2`. A polygon slack matrix is entrywise nonnegative and has ordinary rank exactly `dim(P)+1=3`.

The published lower bound of Gouveia–Robinson–Thomas, *Worst-Case Results for Positive Semidefinite Rank*, **Mathematical Programming** 153 (2015), 201–224, Theorem 2.1 (arXiv:1305.4600) says that any generic `d`-dimensional polytope with `v` vertices has PSD rank at least `(dv)^(1/4)`. Thus here

\[
\operatorname{rank}_{\rm psd}(M^{(m)})\ge(2m)^{1/4}.
\]

Apply the same interpolation theorem to these nonnegative matrices. It produces **SOS bivariate polynomials** `p_m` with

\[
\boxed{\operatorname{rank}(p_m)=3,\quad
\operatorname{sos-rank}(p_m)\ge(2m)^{1/4}\longrightarrow\infty.}
\]

So no uniform function of ordinary rank bounds SOS rank, proving Conjecture 46(iii).

The entries and hence coefficients of the resulting polynomials may be real and transcendental; Conjecture 46 is stated over `R[x,y]`, so this matches the hypothesis. The first family uses rational coefficients.

## Reference

The PSD rank lower bound for generic polygons is Theorem 2.1 of [Gouveia–Robinson–Thomas, Worst-Case Results for Positive Semidefinite Rank](https://arxiv.org/abs/1305.4600).
