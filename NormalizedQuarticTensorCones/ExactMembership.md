# Normalized symmetric tensor cones: exact sign-moment structure, NP-complete membership, and exponential LP complexity

**Date:** 2026-11-11

**Status:** Self-contained informal proofs, with one imported published NP-completeness theorem and one imported published extension-complexity theorem. The claims about novelty have not undergone peer review or an exhaustive priority audit.

**Primary published open question:** Chuyang Ke and Jean Honorio, *Exact Partitioning of High-order Models with a Novel Convex Tensor Cone Relaxation*, *Journal of Machine Learning Research* 23(284), 2022, Section 4, Section 7, and Appendix C: https://www.jmlr.org/papers/volume23/22-0232/22-0232.pdf

## A. Scope and motivation

Ke and Honorio explicitly ask whether deciding membership in the Carathéodory symmetric tensor cone is NP-hard and whether the constrained cone programs in their paper are efficiently solvable. They prescribe an entire family of tensor entries to be one and impose a balancing moment. The unconstrained fourth-power cone was **already** shown NP-hard by Jiang, Li, and Zhang (published in *Foundations of Computational Mathematics*, 2017, Proposition 5.3). The genuinely interesting target is the **normalized slice** subject to the paper's exact constraints.

The results below give an explicit description of that slice, a polynomial-time many-one reduction proving NP-completeness of membership at order 4 **even with balance**, and an unconditional exponential linear extended-formulation lower bound. They also identify why a convex relaxation in the paper is in fact an exact convex-hull formulation for every even tensor order at least 4.

## B. Definitions

For even integer `m` and dimension `D`, let `Sym^m(R^D)` be the space of fully symmetric order-`m` real tensors. Let

\[
\mathcal V^{D,m}=\operatorname{cone}\{v^{\otimes m}:v\in\mathbb R^D\}.
\]

This is the Carathéodory symmetric tensor cone of the paper (the paper allows at most `dim Sym^m(R^D)+1` summands).

Define the **paired-index normalized slice**

\[
\mathcal P_{D,m}=\bigl\{T\in\mathcal V^{D,m}:
 T_{i_1i_1\cdots i_{m/2}i_{m/2}}=1\quad
 \forall i_1,\ldots,i_{m/2}\in[D]\bigr\}.
\]

The entry equation includes all permutations because the tensor is symmetric. Define the **balanced slice**

\[
\mathcal P^{\mathrm{bal}}_{D,m}=
\{T\in\mathcal P_{D,m}:\langle T,\mathbf 1^{\otimes m}\rangle=0\}.
\]

The balance condition is exactly the paper's condition in its conic program (3).

## C. Exact sign-moment theorem (all even orders at least 4)

**Theorem 1.** If `m >= 4` is even, then

\[
\boxed{\mathcal P_{D,m}=
\operatorname{conv}\{s^{\otimes m}:s\in\{\pm1\}^D\}.}
\tag{1}
\]

If `D` is even, then

\[
\boxed{\mathcal P^{\mathrm{bal}}_{D,m}
=\operatorname{conv}\{s^{\otimes m}:
 s\in\{\pm1\}^D,\;\sum_i s_i=0\}.}
\tag{2}
\]

If `D` is odd, the balanced slice is empty.

### Proof

Take any `T` in the normalized cone and write

\[
T=\sum_{h=1}^r v_h^{\otimes m}.
\]

For any coordinates `i,j`, the constraints imply

\[
\sum_h |v_{h,i}|^m=1,\qquad
\sum_h|v_{h,j}|^m=1,\qquad
\sum_h|v_{h,i}|^{m-2}|v_{h,j}|^2=1.
\]

The last identity is the prescribed entry with `m-2` occurrences of `i` and two of `j`; both multiplicities are even. Hölder's inequality yields

\[
\sum_h|v_{h,i}|^{m-2}|v_{h,j}|^2
\le \left(\sum_h|v_{h,i}|^m\right)^{(m-2)/m}
     \left(\sum_h|v_{h,j}|^m\right)^{2/m}=1.
\]

Equality holds. The equality condition in Hölder implies that the two sequences `(|v_{h,i}|^m)_h` and `(|v_{h,j}|^m)_h` are proportional. Since both sums equal one, they are identical. Thus for every `h` and every `i,j`,

\[
|v_{h,i}|=|v_{h,j}|.
\]

Consequently `v_h=c_h s_h` with `c_h >= 0` and `s_h` a sign vector (zero terms may be discarded). Setting `w_h=c_h^m`, we have

\[
T=\sum_h w_h s_h^{\otimes m},\qquad
\sum_h w_h=T_{i\ldots i}=1.
\]

That proves the forward direction of (1). Conversely, every sign tensor has all prescribed even-multiplicity entries equal to one, as do their convex combinations. Carathéodory's theorem bounds the number of terms by the paper's allowed bound.

For the balance condition, observe that for even `m`,

\[
\langle T,\mathbf1^{\otimes m}\rangle
=\sum_h w_h\left(\sum_i s_{h,i}\right)^m.
\]

Each summand is nonnegative. Their sum vanishes precisely when every sign vector with positive weight is balanced. This proves (2). QED.

**Important exception.** For `m=2` the analogous normalized slice is the elliptope of PSD correlation matrices, rather than the sign-correlation polytope; the Hölder-equality step above does not apply. The structural threshold occurs between orders 2 and 4.

## D. Exact rational many-one reduction: balanced membership is NP-complete at order four

Let

\[
\operatorname{COR}(n)=\operatorname{conv}\{xx^{\mathsf T}:x\in\{0,1\}^n\}
\]

be the Boolean correlation polytope. Membership for rational input is NP-complete (Pitowsky, 1991). We reduce this problem to deciding whether a **fully symmetric rational order-four tensor satisfying every paired-index constraint and the balancing constraint** belongs to the Carathéodory cone.

### D.1 Convert Boolean moments to sign correlations

For rational symmetric input `M` of size `n x n`, define a symmetric `N x N` matrix `X`, with `N=n+1` and indices `0,1,...,n`, by

\[
X_{00}=1,\qquad X_{ii}=1,
\]

\[
X_{0i}=X_{i0}=2M_{ii}-1,
\]

and for distinct `i,j >= 1`,

\[
X_{ij}=4M_{ij}-2M_{ii}-2M_{jj}+1.
\tag{3}
\]

Then

\[
\boxed{M\in\operatorname{COR}(n)
\iff X\in\operatorname{CUT}^{\pm}(N)
:=\operatorname{conv}\{ss^{\mathsf T}:s\in\{\pm1\}^N\}.}
\tag{4}
\]

For the forward direction, given random `b in {0,1}^n` with `E b_i b_j=M_ij`, put `s_0=1` and `s_i=2b_i-1`. Equation (3) is then exactly `X_ij=E s_i s_j`. For the reverse direction, given random signs `s` realizing `X`, let `b_i=(1+s_0 s_i)/2`; the moments recover `M`. Thus (4) holds without any extra assumptions on the rational input.

### D.2 Create a balanced fourth-order moment table

Use `D=4N` coordinates indexed by triples

\[
a=(i,b,\varepsilon),\qquad i\in\{0,\ldots,N-1\},\quad b\in\{0,1\},\quad\varepsilon\in\{+1,-1\}.
\]

We now construct **every tensor entry explicitly** from the input `X`, in polynomial time. For an ordered four-tuple of coordinate labels `(a_1,a_2,a_3,a_4)`, let

* `e = product of its four epsilon labels`;
* `d_i = number of labels in the tuple belonging to group i`;
* `E = {i : number of labels with group i and b=1 is odd}`.

Define the fully symmetric tensor `T=T(X)` by

\[
T_{a_1a_2a_3a_4}=e\cdot
\begin{cases}
0,&\text{some }d_i\text{ is odd};\\
1,&\text{all }d_i\text{ even and }E=\varnothing;\\
X_{ij},&\text{all }d_i\text{ even and }E=\{i,j\},\ i\ne j;\\
0,&\text{otherwise}.
\end{cases}
\tag{5}
\]

Only `0, +1, -1, +X_ij, -X_ij` appear. The output has `D^4=O(n^4)` ordered entries and polynomial bit length.

**Lemma 2 (normalization and balance for every rational input).** For all input `X`, even those that are not sign correlation matrices,

\[
T_{aabb}=1 \quad(\forall a,b),
\qquad
\langle T,\mathbf1^{\otimes4}\rangle=0.
\]

For normalization, each label appearing twice has an even group count and even `b` parity, and its epsilon signs multiply to `+1`, so (5) gives one.

For balance, use formal indeterminates `s_i` with identities `s_i^2=1`, and independent formal sign variables `r_i` with `r_i^2=1`. Define formal output coordinates

\[
y_{(i,b,\varepsilon)}=\varepsilon r_i s_i^b.
\]

The coordinates sum to zero identically because the two values of `epsilon` cancel for each `(i,b)`:

\[
\sum_{i,b,\varepsilon}y_{(i,b,\varepsilon)}=0.
\]

Average fourth products formally over the independent `r_i`. After this averaging, only monomials `1`, `s_i`, and `s_i s_j` can survive: a nonzero fourth product has even occurrences of each `r_i`, so either one group occurs four times or two groups occur twice each. Apply the linear functional `L(1)=1`, `L(s_i)=0`, `L(s_i s_j)=X_ij` for `i!=j` (with `s_i^2=1`). The resulting tensor is exactly (5). Applying this functional to the identically zero fourth power of the sum gives the balancing equation for **every** `X`.

### D.3 Exact if-and-only-if

**Theorem 3 (many-one reduction).** For the construction above,

\[
\boxed{M\in\operatorname{COR}(n)
\quad\iff\quad
T(X(M))\in\mathcal P^{\mathrm{bal}}_{4(n+1),4}.}
\tag{6}
\]

**Forward direction.** Suppose `X=E ss^T` for random sign vector `s`. Replace the law of `s` by its equal mixture with `-s`; this preserves `X` but makes `E s_i=0`. Independently select uniformly random signs `r_i` and set

\[
y_{(i,b,\varepsilon)}=\varepsilon r_i s_i^b.
\]

Every realization of `y` has all coordinates in `{±1}` and satisfies `sum_a y_a=0`. Computing `E y_{a_1}...y_{a_4}` by independence of `r` and the centered sign distribution gives precisely (5). Thus

\[
T(X)=\mathbb E[y^{\otimes4}]
\in\mathcal P^{\mathrm{bal}}_{D,4}.
\]

**Reverse direction.** Suppose `T(X)` belongs to the normalized Carathéodory cone. Theorem 1 gives a random sign vector `y` with `T(X)=E[y^{\otimes4}]`. Define `z_i=y_{(i,0,+1)}y_{(i,1,+1)}`, so `z_i in {±1}`. The four coordinates

\[
(i,0,+1),\ (i,1,+1),\ (j,0,+1),\ (j,1,+1)
\]

have even group counts and odd `b` parity in exactly groups `i,j`; hence by (5), for `i != j`,

\[
\mathbb E[z_i z_j]
=T_{(i,0,+1),(i,1,+1),(j,0,+1),(j,1,+1)}
=X_{ij}.
\]

Also `E z_i^2=1=X_ii`. Therefore `X=E zz^T`, so `X` is in the sign-correlation polytope. Equation (4) implies `M in COR(n)`. QED.

### D.4 NP membership

Any normalized feasible rational order-four tensor is a convex combination of at most

\[
1+\binom{D+3}{4}
\]

sign tensors by Carathéodory's theorem. All vertices are integer arrays with entries `±1`. If a rational tensor lies in their convex hull, there exists a basic feasible convex combination with rational weights of polynomial encoding length, by Cramer's rule and determinant bounds for rational linear systems. An NP certificate consists of these sign vectors and rational weights; the verifier checks normalization, balance, and equality with each tensor entry using exact arithmetic.

Combining NP membership with the polynomial many-one reduction and Pitowsky's NP-completeness theorem proves:

\[
\boxed{\textbf{Balanced, paired-normalized symmetric order-four tensor-cone membership is NP-complete.}}
\tag{7}
\]

This is a **strong-membership** decision statement for rational inputs. No claim is made about approximation with a prescribed numerical tolerance.

## E. The paper's conic program is an exact convex-hull formulation (but hard to optimize)

Theorems 1 and 3 are stronger than standalone membership hardness. In the notation of program (3) in Ke–Honorio, for each even `m >= 4` the feasible set is exactly

\[
\operatorname{conv}\{y^{\otimes m}: y\in\{\pm1\}^D,\ \mathbf1^T y=0\}.
\]

Therefore for any objective tensor `W`, one has the exact identity

\[
\boxed{\max_{T\in\mathcal P^{\mathrm{bal}}_{D,m}}\langle W,T\rangle
=\max_{y\in\{\pm1\}^D,\ \mathbf1^T y=0}\langle W,y^{\otimes m}\rangle.}
\tag{8}
\]

Thus the conic formulation is the *exact convex hull* of the original discrete feasible points, not a loose outer relaxation. There is no integrality gap in objective value, although a linear objective may have a nonunique face of optimal mixtures rather than one rank-one solution.

For every even `m >=4`, one can encode an arbitrary quadratic objective `\sum_{i<j}c_{ij} y_i y_j` by setting the symmetric tensor coefficient of the monomial `y_i^{m-1}y_j` to `c_ij`: on sign vectors, `y_i^{m-1}y_j=y_i y_j`. Consequently **balanced minimum bisection** reduces to linear optimization over the slice (8). This proves NP-hardness of its exact optimization for any fixed even order `m>=4` (assuming variable even dimension).

In particular, simply expressing the original problem using a convex cone does not yield an efficient exact optimization algorithm.

## F. Exponential LP extension complexity (unconditional)

The normalized slice `P_{D,4}` is a polytope, not merely an arbitrary semialgebraic cone section.

For every sign tensor `s^{⊗4}`, its coordinates `(s^{⊗4})_{iiij}=s_i s_j`. Thus the linear projection

\[
\pi(T)_{ij}=T_{iiij}\quad (i\ne j),\qquad \pi(T)_{ii}=1
\]

maps the normalized slice **onto** the sign-correlation/cut polytope on `D` vertices. Fiorini–Massar–Pokutta–Tiwary–de Wolf (JACM 2015) prove an exponential extension-complexity lower bound for the cut polytope. Therefore

\[
\boxed{\operatorname{xc}(\mathcal P_{D,4})\ge 2^{\Omega(D)}.}
\tag{9}
\]

For the **balanced** slice on `D=4n` variables, use the projection

\[
\pi_{\mathrm{bal}}(T)_{ij}=
T_{(i,0,+1),(i,1,+1),(j,0,+1),(j,1,+1)} \quad (i\ne j).
\]

Every balanced sign tensor projects to a sign-correlation matrix of `z_i=y_{(i,0,+1)}y_{(i,1,+1)}`. Conversely every sign vector `z` can be lifted to a balanced `y` by using `y_{(i,0,+)}=1`, `y_{(i,1,+)}=z_i` and the corresponding negative companion values. Hence the projection of the whole balanced polytope is the cut correlation polytope. It follows that

\[
\boxed{\operatorname{xc}(\mathcal P^{\mathrm{bal}}_{4n,4})\ge2^{\Omega(n)}=2^{\Omega(D)}.}
\tag{10}
\]

This prohibits polynomial-size **linear extended formulations**, even with auxiliary variables, unconditionally. It does not imply a corresponding lower bound on arbitrary semidefinite programming lifts.

## G. Small exact check

For `n=2`, a sign-correlation matrix with off-diagonal entry `1/3` is realized by a distribution on `(s_1,s_2)` with probabilities `(1+(1/3)s_1s_2)/4`. The balanced construction has `D=8`. An exact rational implementation enumerated all `binom(8+3,4)=330` distinct symmetric fourth-order entries, verified each against the direct average over sign assignments, and checked every paired-index entry, the opposite-companion identities, and balance for each sampled sign vector. The verification program is supplied separately as `check_tensor_slice.py`.

This finite test validates the implementation, not the general proof, which is symbolic.

## H. A tensor-isomorphism bridge: the exact linear symmetry group of the normalized slice

**Theorem 5 (monomial rigidifier).** Fix even `m >= 4` and `D >= 2`. Under the diagonal action of `GL_D(R)` on symmetric order-`m` tensors,

\[
\boxed{\{g\in\mathrm{GL}_D(\mathbb R):g^{\otimes m}\mathcal P_{D,m}=\mathcal P_{D,m}\}
=\{\text{signed permutation matrices}\}.}\tag{11}
\]

**Proof.** By Theorem 1, the vertices of the slice are exactly the sign tensors `s^{⊗m}` (where `s` and `-s` give the same vertex). To see that each is an exposed vertex, use the linear functional `L_s(T)=<s^{⊗m},T>`. At a sign vertex `t^{⊗m}`, its value is `(s^T t)^m`, which is at most `D^m`, with equality only when `t=+s` or `t=-s`. Thus the vertices are precisely those sign tensors.

If `g^{⊗m}` preserves the entire polytope, it permutes its exposed vertices. Consequently, for every sign vector `s`, `(gs)^{⊗m}=t^{⊗m}` for some sign vector `t`. Over the reals and for even `m`, this implies `gs=±t`. Hence `g` takes every vertex of the hypercube `{±1}^D` to a vertex of that same hypercube.

Fix any row `a` of `g`. Then `\ell(s)=\sum_j a_j s_j` is in `{±1}` for every sign vector `s`, so `\ell(s)^2` is identically 1 as a Boolean polynomial. Expanding,

\[
\ell(s)^2=\sum_j a_j^2+2\sum_{j<k}a_j a_k s_j s_k.
\]

Uniqueness of Fourier coefficients on the sign cube implies `a_j a_k=0` whenever `j != k`, and `\sum_j a_j^2=1`. Thus every row has exactly one nonzero entry, of magnitude one. Since `g` is invertible, different rows must select different columns. Therefore `g` is a signed permutation matrix. The converse is immediate because such matrices permute sign vectors. QED.

This shows that the normalized tensor slice **rigidifies a full real general-linear action down to a finite monomial group**. That is a potentially reusable ingredient for reductions concerning tensor stabilizers and isomorphism. It does **not**, without further gadgets, prove a TI-completeness result.

## I. Relation to tensor isomorphism and future reductions

The reduction demonstrates a transferable **finite constraint gadget**: fourth-order symmetric moments with all paired-index entries frozen to 1 force positivity witnesses to lie in the sign cube, and additional linear tensor entries encode the full Boolean correlation polytope. Unlike encoding only quadratic forms, this operates inside a genuinely high-order fully symmetric tensor space under a large prescribed coefficient family.

Potential future research is to make the gadget invariant under an appropriate group action (e.g. a colored or parabolic tensor-isomorphism action). That is **not** obtained here: membership/optimization hardness does not imply TI-completeness or an isomorphism reduction.

The only techniques transferred from the Yang–Mills proof program are structural rather than technical dependence: insist on one common positive witness, preserve exact constrained moments through symmetrization, and treat nonlinear limits/constraint closure precisely. No Yang–Mills theorem is used.

## J. References and priority cautions

1. Ke, C. and Honorio, J. (2022). *Exact Partitioning of High-order Models with a Novel Convex Tensor Cone Relaxation*. JMLR 23(284), 1–28. Sections 4, 7, Appendix C. https://www.jmlr.org/papers/volume23/22-0232/22-0232.pdf
2. Pitowsky, I. (1991). *Correlation polytopes: Their geometry and complexity*. Mathematical Programming 50, 395–414. DOI: 10.1007/BF01594946 (verify DOI separately if citing formally); established NP-completeness of rational correlation-polytope membership.
3. Jiang, B., Li, Z. and Zhang, S. (2017). *On Cones of Nonnegative Quartic Forms*. Foundations of Computational Mathematics 17, 161–197, Proposition 5.3. DOI: 10.1007/s10208-015-9286-4. This **already** proves unrestricted sums-of-fourth-powers cone membership NP-hard; do not portray it as a new result.
4. Fiorini, S., Massar, S., Pokutta, S., Tiwary, H.R., and de Wolf, R. (2015). *Exponential Lower Bounds for Polytopes in Combinatorial Optimization*. JACM 62(2), Article 17. DOI: 10.1145/2716307.
5. Caprara, A., Furini, F., Gentile, C., Liberti, L. and Lodi, A. (2026). *Hardness of some optimization problems over correlation polyhedra*, Optimization Online (preprint); independently notes Karp-reduction hardness for cut-polytope membership. https://optimization-online.org/2026/03/hardness-of-some-optimization-problems-over-correlation-polyhedra/

**Priority caution:** Targeted searches did not uncover a later solution of the *paired-normalized, balanced Carathéodory tensor-cone membership* question, but the literature audit is not exhaustive. The manuscript therefore establishes a proposed resolution of the specific 2022 question, not proven historical priority. Its exact math can be checked independently from equations (1)–(11). It is not a VP/VNP or tensor-isomorphism complexity-class separation.
