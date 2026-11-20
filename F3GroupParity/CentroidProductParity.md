# One ordinary isomorphism comparison for parity across centroid factors

Work over $F=\mathbb F_3$. A compact special exponent-three group is given by its alternating bracket $\beta:X\times X\to Z$, whose values span $Z$ and whose common radical is zero. The group law on $X\oplus Z$ is addition plus $\beta/2$ in the central coordinate. Each group isomorphism comes from invertible $g:X\to X'$ and $h:Z\to Z'$ with
$$
\beta'(gx,gy)=h\beta(x,y),
$$
and a central shear which has determinant one. The sign of the resulting permutation of the group elements in the coordinate order is $\det(g)\det(h)$, with $-1\in F$ identified with the odd sign. This follows from the Zolotarev–Frobenius formula on the additive space. Every left translation has odd order. Normalizing a regular permutation conjugator by a left translation therefore turns it into a group isomorphism of the same sign. Even group isomorphism is consequently the required $A_N$ conjugacy question in the compact model. [Brunyate and Clark, sign of a finite-field linear map](https://plclark.github.io/PeteLClark/Research/Brunyate-Clark_final.pdf).

## Main theorem

Let $L\ge2$ be the total dense input bit length. Decompose both brackets into their intrinsic direct factors by the centroid, as below. Fix a constant $c$. Suppose every indecomposable factor satisfies at least one of these two conditions.

1. Its quotient dimension $\dim X_i$ is odd.
2. The kernel of its induced linear map $\bigwedge^2 X_i\to Z_i$ has dimension at most $c\log_2 L$.

Suppose also that every ordinary isomorphism type of even additive dimension occurs at most once on each side, except for types possessing an odd automorphism. There is then a deterministic polynomial-time many-one reduction from even isomorphism of the two compact groups to ordinary TI over $F$. This gives one ordinary compact group-isomorphism instance, hence one ordinary $S_N$ conjugacy query in the compact model with the target group order allowed to change. There is no bound on the number of odd-dimensional factors or on their ordinary isomorphism multiplicities. The case where every factor has odd additive dimension needs only the two displayed local conditions, each recognizable by linear algebra.

The merger applies more generally to any local families with deterministic polynomial-size even-isomorphism comparisons that remain valid after a basis twist. The two stated local cases give unconditional instances of this merger.

## Intrinsic factor recovery

Define the centroid of the bracket to consist of all pairs of linear maps $(a,c)$ on $X,Z$ with
$$
\beta(ax,y)=\beta(x,ay)=c\beta(x,y).
$$
These are linear equations. Both projections of this algebra into its matrix realizations are injective: a zero $c$ forces $a=0$ by the zero common radical, and a zero $a$ forces $c=0$ since the bracket values span $Z$. The pairs are closed under composition since for $(a,c)$ and $(b,d)$ one has
$$
cd\beta(x,y)=c\beta(bx,y)=\beta(bx,ay)=d\beta(x,ay)=dc\beta(x,y).
$$
This proves $cd=dc$, and then $ab=ba$ by the same radical condition. The centroid is a finite-dimensional commutative unital $F$-algebra.

Its primitive idempotents are computable in deterministic polynomial time over $F$. Write $J$ for the nilradical. If $3^t\ge\dim_F C$, then $J$ is the kernel of the $F$-linear map $u\mapsto u^{3^t}$. Each nilpotent element has nilpotence index at most the dimension, as seen from multiplication on $C$. The quotient is a product of finite fields. Its Frobenius-fixed algebra is $\mathbb F_3^k$ for the number $k$ of field factors. Compute this subalgebra by the kernel of $u^3-u$ in the quotient. Split it into simultaneous eigenspaces of multiplication by its basis elements, using the three possible eigenvalues. Distinct coordinate projections cannot agree on every basis element. Thus the resulting simultaneous spaces are the one-dimensional coordinate ideals. Project $1$ to recover their idempotents. For any representative $b$ of such an idempotent, $b^{3^t}$ is an idempotent lift, since $(b^2-b)^{3^t}=0$. The lift is unique because equality modulo $J$ for any two idempotents becomes equality after the same Frobenius power.

For an idempotent $(a,c)$, its images and kernels give two complementary factor brackets. For $x$ in $\operatorname{im}a$ and $y$ in $\ker a$, $\beta(x,y)=\beta(ax,y)=\beta(x,ay)=0$. The image bracket takes values in $\operatorname{im}c$ and spans it; the analogous statement holds on the kernels. Both common radicals are zero because cross brackets vanish. Conversely a direct factor decomposition gives the corresponding centroid projections. Hence the primitive idempotents determine precisely the indecomposable factor brackets $\beta_i:X_i\times X_i\to Z_i$. Every bracket isomorphism conjugates the centroid action and permutes the factors, and every matching of factor isomorphisms assembles to a bracket isomorphism. [Wilson, direct product decomposition via bilinear maps and commutative rings](https://arxiv.org/abs/1005.0548).

Use an arbitrary deterministic ordering of the factors and bases in each $X_i,Z_i$. Let $D_i=\dim X_i+\dim Z_i$. On each endpoint concatenate the bases of $X_i\oplus Z_i$ in factor order and compute the determinant of the resulting full frame in the given additive coordinates. Write $\kappa$ for the ratio of the target and source frame determinants. For a matching $\pi$ and local signs $s_i$ in the chosen factor bases, the raw sign of the isomorphism is
$$
\kappa\cdot (-1)^{\#\{(i,k): i<k,\ \pi(i)>\pi(k),\ D_i,D_k\ \text{odd}\}}
  \prod_i s_i.
$$
Only odd dimensions enter the permutation sign because transposing blocks of dimensions $D_i,D_k$ contributes $(-1)^{D_iD_k}$.

## Base comparisons

For $\dim X_i$ odd, the actual automorphism $(-I_{X_i},I_{Z_i})$ has odd sign. Thus every ordinary match into such a factor admits both signs. An ordinary comparison suffices.

For the small kernel case, put $n=\dim X_i$, $K=\ker(\bigwedge^2 X_i\to Z_i)$, and choose a basis of $K$ followed by lifts of the given center basis. The wedge basis of $X_i$ gives the reference frame for computing this second frame determinant. The dimensions determine which pair of formats ought to match. For a bracket transporter $(g,h)$, let $g_K$ be the induced map on $K$. Since $\det(\bigwedge^2 g)=(\det g)^{n-1}$, the exact sequence gives
$$
\det(g)\det(h)=
\frac{(\det g)^n}{\eta\,\det g_K},
$$
where $\eta$ is the target-to-source ratio of those wedge frame determinants. The determinant formula for $\bigwedge^2 g$ follows over an algebraic closure by triangularizing $g$, then taking its diagonal products. If $n$ is even the numerator is one over $F$. We can therefore test either sign by marking the appropriate nonzero vector on $\bigwedge^{\dim K}K$, using the computed $\eta$. For $\dim K=0$, evaluate the sole possible $K$ determinant directly.

To force the line action, register the bracket, the induced wedge-square map, and the inclusion of $K$ in that wedge square. Link all exterior powers of $K$ by wedge multiplication. The entire auxiliary exterior algebra has dimension $2^{\dim K}$. An isomorphism of this diagram acts on its wedge-square role by $\bigwedge^2 g$ and on all the exterior degrees of $K$ by the induced maps, since products of degree-one elements span them. The variable number of degrees is packed into one role using grading projections. The mark on the top line then tests exactly the desired sign. The roles and map kinds are fixed. The ordinary tensor-system compiler produces an ordinary three-tensor comparison in polynomial time. An odd target sign can also be tested by twisting one target basis vector by $-1$ and using an even comparison. This preserves the stated base hypotheses. [Chen, Grochow, Qiao, Tang and Zhang, Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4).

## Combining local signs and permutations without searching for a matching

Let $I_{ij}$ test ordinary isomorphism of source factor $i$ to target factor $j$. Let $E_{ij}$ and $O_{ij}$ test signs $+1$ and $-1$ in their displayed factor bases. Tests at incompatible formats are constant false. Use an ordinary comparison of the two full brackets as a global guard. The following positive branch also uses tests among the target factors themselves. It detects a genuine odd automorphism if either

- a target factor admits an odd automorphism, or
- two distinct target factors of odd additive dimension are ordinarily isomorphic.

In the latter case swap the factors using one isomorphism and its inverse. The local determinant product is one and the block swap contributes $-1$. If the global guard and this branch are true, an arbitrary isomorphism can be repaired to even parity by composing with the detected odd automorphism.

On inputs where the global guard is true and this branch is false, the assumed condition on even types ensures that every source factor has exactly one ordinarily isomorphic target factor. Indeed all odd types are distinct on the target, and any repeated even type would supply an odd automorphism by hypothesis. No local matching has both signs, since two opposite-sign witnesses would give an odd target automorphism. Thus the following pairs of tests are genuine complementary truth values in this case.

- For each $i$, the odd local-sign test is $\bigvee_j O_{ij}$, and the even local-sign test is $\bigvee_j E_{ij}$.
- For each $i<k$ whose additive dimensions are both odd, the inversion test is $\bigvee_{j>l}(I_{ij}\wedge I_{kl})$, and the non-inversion test is $\bigvee_{j<l}(I_{ij}\wedge I_{kl})$.

No branch enumerates any matching. Use a balanced binary tree to combine these sign bits. If child pairs are $(e_1,o_1)$ and $(e_2,o_2)$, the parent tests are
$$
((e_1\wedge e_2)\vee(o_1\wedge o_2),\
 (e_1\wedge o_2)\vee(o_1\wedge e_2)).
$$
The empty list gives the constant even bit. Use the even root if $\kappa=1$ and the odd root otherwise. This is exactly the required raw sign formula on the promised case. The full test is the global guard AND the OR of the odd-automorphism branch and the selected sign test. On any pair where the global guard fails, the output is negative. On any pair where the guard and odd-automorphism branch pass, the output is positive regardless of the values in the sign tree. This explains why the sign tests need only be complementary on the specified case.

Every constituent test is an ordinary TI comparison or a constant. Ordinary TI has constant-input positive AND and OR gadgets with constant-factor side-length growth. For AND, compare two ordered pairs of structures with marked components. For OR of $a\cong b$ and $c\cong d$, compare the unordered pairs of tagged ordered structures $\{(a,c),(b,d)\}$ and $\{(a,d),(b,c)\}$. Straight matching tests $c\cong d$ and crossed matching tests $a\cong b$. The [explicit triangular-algebra implementation](CenterAndKernel.md#compilation-and-branch-combination) gives the linear side bound for OR. Its ordered product gives the AND bound. The positive formula above has depth $O(\log L)$ after balancing its disjunctions and the sign tree, and each leaf comparison has polynomial side lengths. Unrolling at logarithmic depth and applying the constant-growth gadgets gives one ordinary TI pair of polynomial size. [Grochow and Qiao, linear-length tensor gadgets](https://arxiv.org/abs/2306.16317).

For the ordinary compact group output, use the reduction from ordinary TI to alternating matrix-space isometry in the same paper. Pass its alternating forms to the quotient by their common radical, preserving the dimension of that radical as a test. A quotient isometry extends along any bases of the radicals, and any original isometry preserves them. Independent forms give a surjective bracket to their dual coordinate space and removing the common radical gives the special-group hypotheses. Trivial cases can be sent to fixed valid positive or negative compact group comparisons. The Baer law then returns the desired ordinary group problem.

## An unbounded example with real sign constraints

Take $n\equiv2\bmod 4$ and a two-dimensional subspace $K\subset\bigwedge^2 X$, where $\dim X=n$. Set $Z=(\bigwedge^2 X)/K$ with its natural bracket. It is surjective. For $x\ne0$, the subspace $x\wedge X$ has dimension $n-1>2$, so the bracket radical is zero. Any decomposition $X=X_1\oplus X_2$ into two nonzero bracket factors would force $X_1\wedge X_2\subseteq K$. Its dimension is at least $n-1$, a contradiction. Thus this is a single centroid factor. Its additive dimension $n+\binom n2-2$ is odd.

For explicit sign-rigid examples of this form, divide $X$ into four even blocks of dimensions $2b_i$, with distinct positive $b_i$ summing to $n/2$. On each block fix a nondegenerate alternating bivector $\omega_i$. For each of the four projective points of $\mathbf P^1(F)$ take one linear form $\ell_i$ with that kernel. Define the bivectors in $K$ as $\sum_i\ell_i(u,v)\omega_i$ for $(u,v)\in F^2$. Each projective bivector line has a distinct rank drop $2b_i$, forcing every induced map on $K$ for an automorphism to fix all four lines. Such a map is scalar and its determinant is one. The kernel determinant formula then gives even sign for every automorphism. A basis twist of determinant $-1$ gives an ordinary match with no even transporter. Distinct unordered quadruples $(b_i)$ of a common sum give different ordinary types in the same format, witnessed by their kernel rank-drop magnitudes. The theorem applies to products of these groups with no bound on the number of factors of that common format. Underlying ordinary isomorphism may permute the summands, and the sign tree tests the resulting parity.

The result proves a same-field many-one reduction for its specified class. It does not prove the unrestricted reverse reduction of [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5).
