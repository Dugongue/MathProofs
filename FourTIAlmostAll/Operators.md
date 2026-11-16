# Crossed inverse covariants for binary four-tensor isomorphism

Let $T\in V_1\otimes V_2\otimes V_3\otimes V_4$ with $V_i=k^n$, and suppose that at least one of its three pair flattenings is invertible. A pair flattening is indexed by a pair of modes for its rows and the complementary pair for its columns. For each invertible cut $s$, reshuffle its inverse transpose into a contravariant four-tensor $S_s$. For a pair $i,j$ crossing the cut $s$, contract $T$ and $S_s$ on the other two modes to form
$$
 C_{ij,s}\in\operatorname{End}(V_i\otimes V_j).
$$
In coordinates with the other two indices denoted by $r,t$, this is
$$
 (C_{ij,s})_{a b,a' b'}=\sum_{r,t}T_{a b r t}(S_s)_{a'b'rt}.
$$
Define the one-mode anchor from this pair by
$$
 E_{i;j,s}(T)=\operatorname{Tr}_{V_j}(C_{ij,s}^2).
$$
The contraction is a genuine partial trace of a squared endomorphism. The order of the steps matters: tracing $C_{ij,s}$ itself gives $nI$ in either remaining mode.

## 1. Exact transporter recovery

If $g=(g_1,g_2,g_3,g_4)$ is an invertible mode change, $S_s(gT)$ is transformed by the contragredient mode actions. This follows by applying $(AXB)^{{-T}}=A^{{-T}}X^{{-T}}B^{{-T}}$ to a flattening. Hence $C_{ij,s}(gT)$ is conjugate to $C_{ij,s}(T)$ by $g_i\otimes g_j$, and
$$
 E_{i;j,s}(gT)=g_iE_{i;j,s}(T)g_i^{-1}.
$$
The last equality follows from cyclicity in the traced mode.

**Theorem.** Over $\mathbb F_2$, ordinary four-tensor isomorphism has a deterministic polynomial-time exact search and decision algorithm on every first input for which, in each of the four modes, the joint commutant of the explicitly defined anchor tuple has dimension one. The converse input is arbitrary. One may use just a prescribed invertible cut and the two crossed anchors in each mode. One may also use all three cuts and the four crossed anchors in each mode.

To find the joint commutant, solve the linear equations $XE=EX$ in the $n^2$ entries of an unknown endomorphism $X$. On accepted first inputs compare the corresponding anchor tuples of the two tensors by the linear equations $XE_i=E'_iX$. If the second input lacks an inverse cut present in the first input, the two cannot be isomorphic. If the tensors are isomorphic, the four intertwiners include the actual mode maps. An invertible intertwiner $X_0$ identifies the full intertwiner space with $X_0$ times the source commutant. Thus an isomorphism implies that every intertwiner space is one-dimensional and its unique nonzero binary element is invertible. If any such condition fails, return inequivalence. Otherwise use the four unique nonzero solutions, and return equivalence precisely when their action on the first tensor gives the second. This last verification handles the possibility that the anchors match while the tensors do not. A source failing the initial commutant test yields abstention. Every computation uses a constant number of matrix inversions, products, contractions and linear solves of polynomial dimensions.

The witness on an accepted binary source is unique when it exists. Indeed a stabilizer must centralize the anchor in each mode, and the only invertible scalar over $\mathbb F_2$ is $1$. Over another fixed finite field the same algorithm works by allowing one scalar factor in the final tensor comparison, and the set of stabilizers on a nonzero accepted input has the usual scalar kernel.

## 2. A quadratic formulation of the remaining random-input problem

It suffices to control the anchors from a single invertible cut $12\mid34$. Write its matrix as $A$, and identify $S=A^{-T}$ in the same flattening order. Conditional on this cut being invertible, $A$ is uniform in $\operatorname{GL}_{n^2}(\mathbb F_2)$. It is enough to prove an $o(1)$ failure probability in this distribution. This also bounds the unconditional mass of failures on the all-invertible sector by $o(1)$.

For the mode $3$ anchors, split the first coordinate $a$ into two parts $L,H$ of sizes $\lfloor n/2\rfloor,\lceil n/2\rceil$. Let $X$ be an arbitrary matrix supported on rows $(a,j)$ with $a\in H$ and columns $(b,s)$ with $b\in L$. Here $j,s$ index mode $2$. In particular $X^2=0$. Sample a uniform invertible basis matrix $A_0$, and independently sample all the allowed entries of $X$ uniformly. Set
$$
 A=(I+X)A_0,\qquad S=(I-X)^T A_0^{-T}.
$$
This still makes $A$ uniform in the full invertible group. Crucially, both $T$ and $S$ now depend affinely on the $|L||H|n^2$ independent random bits of $X$ with $A_0$ held fixed.

Write $C_{13}$ as an $n$-by-$n$ block matrix of $n$-by-$n$ operators on mode $3$, indexed by the first mode. Changes in the rows of $T$ are supported in $H$, and changes in the rows of $S$ are supported in $L$. Thus the degrees of the four broader blocks of $C_{13}$, using $L,H$ order, are bounded by
$$
 \begin{pmatrix}
  1 & 0\\
  2 & 1
 \end{pmatrix}.
$$
Only the two diagonal blocks of $C_{13}^2$ contribute to $\operatorname{Tr}_{V_1}(C_{13}^2)$. Their blocks have degree at most two, because each product across the off-diagonal blocks has one factor of degree zero. For $C_{23}$ the index $a$ is contracted between $T$ and $S$. The two variation terms have disjoint support in it, so $C_{23}$ itself is affine-linear in $X$. Thus its squared partial trace on mode $3$ is again quadratic.

For reference, regard each row $T_{aj,-}$ as a matrix $T_{aj}$ in its coordinates on $V_3,V_4$, and use $S_{a j}$ for the reshaped inverse rows. At $X=0$ these are $T^0_{a j},S^0_{a j}$. The two operators before squaring have respective blocks $\sum_jT_{aj}S_{bj}^{T}$ on indices $a,b$, and $\sum_a T_{aj}S_{aj'}^{T}$ on indices $j,j'$. The coefficient of $X_{ar,bs}$ in the second operator is
$$
 \sum_{j'} e_{rj'}\otimes T^0_{bs}(S^0_{aj'})^T
 -\sum_{j}e_{js}\otimes T^0_{bj}(S^0_{ar})^T .
$$
These formulas work with minus signs in arbitrary characteristic. The analogous quadratic conditioning for the other modes uses the same construction after swapping sides of the cut or swapping the two modes within a side. This avoids conditioning on a second random inverse in the proposed estimate.

Here is a sufficient estimate with an exact numerical threshold. In characteristic two, $\operatorname{tr}(C^2)=(\operatorname{tr}C)^2$, and the full contraction for $C$ is $n^2$ in the field. Thus the two anchors in each mode take values in a pair of fixed-trace affine matrix spaces. For coefficient matrices $P,Q$, use the quadratic phase
$$
 f_{P,Q}(X)=\operatorname{tr}\big(P E_{3;1,s}(X)+Q E_{3;2,s}(X)\big).
$$
The corresponding character is constant on the entire pair of trace spaces precisely when both $P,Q$ are scalar. Suppose that, for all but $o(1)$ of the baseline invertible matrices $A_0$, every nonconstant phase has polar form of rank at least $2n^2+\omega(1)$ on the allowed shear entries. This estimate would suffice for $1-o(1)$ coverage.

Indeed, the square of the bias of any quadratic binary phase is at most $2^{-r}$, where $r$ is its polar rank. Expand the square as the average over shifts and then use character orthogonality in the original variable. Parseval and Cauchy–Schwarz on the pair of trace spaces, of dimension $2(n^2-1)$, then give $o(1)$ total-variation distance from two independent uniform matrices on these affine spaces. Averaging over $A_0$ preserves this bound.

Two such independent uniform fixed-trace matrices have scalar joint centralizer with probability $1-o(1)$. One can prove this by first taking independent unconditioned uniform matrices, since the two trace conditions cost a factor four. For a $k$-dimensional proper nonzero coordinate subspace the preservation probability of each random matrix is $2^{-k(n-k)}$. The number of such spaces is at most a fixed constant times $2^{k(n-k)}$ by the Gaussian binomial formula. A union bound gives $o(1)$ for common proper invariant spaces. On an irreducible module the commutant is a finite division ring and hence a field. A nonscalar commutant therefore embeds $\mathbb F_{2^d}$ with $d>1$ dividing $n$. The number of possible embedded field structures is at most $\lvert\mathrm{GL}_n(2)\rvert/\lvert\mathrm{GL}_{n/d}(2^d)\rvert$, since all field-module bases are conjugate. This is $O(2^{n^2(1-1/d)})$ uniformly in $d$. The probability that both random matrices commute with any particular such structure is $2^{-2n^2(1-1/d)}$. Summing over $d$ again gives $o(1)$. Apply this conclusion to each of the four mode pairs of anchors with a union bound.

The joint two-operator estimate remains open here. The [marginal mixing proof](SingleAnchor.md) handles one operator at a time and suffices for the [complete recognition theorem](FullCoverage.md).

## 3. Exact finite controls

The packed-integer implementation in the same directory sampled binary arrays until the requested number with all three pair flattenings invertible was obtained, with a fixed pseudorandom seed for each size. Each commutant was computed by exact elimination of the binary equations. The counts below require scalar joint commutants in all four modes of each accepted tensor.

| Side length | All-invertible samples | Two anchors per mode, one inverse cut | Four anchors per mode, all three inverse cuts |
|---:|---:|---:|---:|
| 3 | 40 | 18 | 40 |
| 4 | 40 | 27 | 40 |
| 5 | 40 | 40 | 40 |
| 6 | 40 | 40 | 40 |
| 8 | 30 | 30 | 30 |
| 10 | 20 | 20 | 20 |

The use of all three cuts passed $210/210$ controls. The one-cut method passed all $130$ controls with side length at least five. These are exact finite computations, with no asymptotic coverage conclusion.

The context is the earlier MathProofs [fixed-field ordinary four-tensor result](https://github.com/Dugongue/MathProofs/blob/main/FixedFieldOrdinaryFourTI/PROOF.md), whose algorithm uses kernel forms on a singular pair flattening, and the [finite-field average-case TI landscape](https://arxiv.org/html/2604.00591v2). The covariants above use a different input feature, namely a true inverse of an invertible flattening. The present work is informal. A priority search and an asymptotic probabilistic audit are separate from the finite checks.
