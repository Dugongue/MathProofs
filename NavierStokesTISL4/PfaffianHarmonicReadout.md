# Compressing the Pfaffian sign by a finite character average

Let $F=\mathbb F_3$. The inputs are ordered three-tensors with square matrix slices, written as linear matrix pencils $M_X(z)$ on label spaces of dimension $r$. A raw transporter $(P,Q,C)$ satisfies
$$ M_Y(Cz)=P M_X(z) Q^{\mathsf T}. $$
The one-sign problem $P_1$ requires $\det P=1$. The problem $P_3$ requires $\det P=\det Q=\det C=1$. The result below applies after permuting the raw modes when the tested mode is the second matrix mode. It gives a sufficient reduction for the finite-field case of the authors' special-linear question. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Theorem

Suppose the first input has a one-dimensional space of right multipliers $B$ such that $M_X(z)B$ is alternating for every $z$, and its multiplier line contains an invertible matrix. Choose any invertible generator $B_X$ and put
$$ p_X(z)=\operatorname{Pf}(M_X(z)B_X). $$
Suppose that $p_X$ is nonzero and splits into linear factors over $F$. For any $p:F^r\to F$, define the integer
$$ I(p)=|\{z:p(z)=1\}|-|\{z:p(z)=-1\}|. $$
Assume $I(p_X)\ne0$. Let $t$ be the largest relation-space dimension of a connected component of the represented matroid of distinct projective factors of $p_X$. Then each of the following is a deterministic single-instance reduction taking $\operatorname{poly}(L)\,3^t$ time, where $L$ is the total dense input length.

- On $P_1$, the output is one ordinary tensor isomorphism comparison.
- On $P_3$, the output is one $P_1$ comparison retaining only the determinant of the original label map $C$.

No target promise, algebraic basis choice, factor ordering correspondence, or transporter is required as input. In particular logarithmic $t$ suffices even if the ambient rank, total nullity, and tensor dimensions grow. The polynomial bound for this class includes the factor-recovery step.

### Direct use of the Navier–Stokes proof

The source's harmonic projection integrates a phase to zero unless its frequency is zero. Below the normalized mean of a character on a finite linear relation space isolates membership in the primal evaluation space by killing every nontrivial character. The character product turns a signed sum over arbitrary label vectors into one over only the relation coordinates. A separate cut-width evaluation uses the source's tree certificate assembly to send partial frequency sums to one parent and close at zero at the root. The input tensor and its determinant constraints determine the equations in the finite model. [Alpöge–Buckmaster's character mean](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/CertCell/AssemblyPotentialModelTorusMeanFacts.lean#L126-L151) · [Tree certificate assembly](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/TreeFinal.lean#L28-L71)

## 1. Raw transporter calibration

The multiplier equations are linear in $B$ and a generator and its invertibility are found by row reduction and a determinant. If $X,Y$ are ordinarily equivalent, then $Y$ inherits this property. Indeed, the alternating condition at $Y$ on $B$ holds exactly when $Q^{\mathsf T}BP^{-\mathsf T}$ is a multiplier at $X$ by invertible congruence. Consequently every actual raw transporter satisfies
$$ M_Y(Cz)B_Y=a P M_X(z)B_XP^{\mathsf T} $$
for a unit $a\in F^\times$. If the matrices have size $2d$, Pfaffian transformation gives
$$ p_Y(Cz)=a^d\det(P)\,p_X(z). $$
This uses the alternating Pfaffian identities over $F$.

If $d$ is odd, the change $z\mapsto-z$ implies $I(p_X)=0$. Under our hypothesis $d$ is even and $a^d=1$. Taking determinants in the raw multiplier equation also gives $\det P=(\det B_Y/\det B_X)\det Q$. This already permits dropping one linked matrix sign in the three-sign problem after calibration. The harmonic readout eliminates the one tested sign into ordinary TI and determines both linked matrix signs. Also replacing an endpoint multiplier generator by its negative leaves its Pfaffian unchanged. Since $C$ is a bijection of label vectors, every raw transporter gives the integer equality
$$ I(p_Y)=\chi(\det P)\,I(p_X),\qquad
 \chi(0)=0,\;\chi(1)=1,\;\chi(-1)=-1 .$$
Thus a single calibrated sign applies to the entire raw transporter set when it is nonempty. This formula applies directly to each original witness, with its other two determinants unchanged.

Compute the two imbalances as below. Failure of any required target computation leads to a fixed NO result. A target ordinarily equivalent to the promised source inherits the Pfaffian splitting, factor structure and nonzero imbalance, and its computations succeed exactly. If $I(p_X)\ne I(p_Y)$ return a fixed NO of the appropriate output problem. For the three-sign comparison also reject when the multiplier determinants at the endpoints differ. Then the calibrated left sign forces the right sign as well. Return the original pair with only the label constraint. For the one-sign comparison return the original pair with no constraints. Soundness on targets outside the promise follows because the output retains the original tensor comparison itself whenever the quick rejection does not apply. If an isomorphism is possible, the imbalance rule gives exactly the dropped sign, so all required soundness and completeness implications hold.

## 2. Deterministic factor recovery on promised inputs

Write
$$ p(z)=c\prod_{i=1}^N\ell_i(z)^{e_i} $$
with distinct projective factors and each $\ell_i$ normalized by its first nonzero coefficient. All $(c,\ell_i,e_i)$ can be recovered with polynomially many Pfaffian evaluations. We recall the split factor-recovery argument for completeness.

Take a ternary extension $K$ of size greater than $r(d+1)^2+d+1$ and at most three times that threshold. Its cardinality is polynomial in the input size. One can enumerate degree-$[K:F]$ monic polynomials until finding an irreducible one by Frobenius gcd tests. On the moment curve $u\mapsto(1,u,\ldots,u^{r-1})$ of $K^r$, every nonzero linear functional has at most $r-1$ zeros. There is a point $a$ on that curve where all factors are nonzero. Find it using Pfaffian evaluations.

On the same curve choose $b$ maximizing the number of distinct roots of $p(b+ta)$ over $t\in K$. This can be done by scanning $b,t$. Outside the zeros of the nonzero linear differences $\ell_i/\ell_i(a)-\ell_j/\ell_j(a)$, all roots $t_i=-\ell_i(b)/\ell_i(a)$ are distinct. There is such a point by the same cardinality bound. Recover the multiplicities by univariate interpolation of degree at most $d$ and division by the roots. For each root $t_i$ and coordinate vector $v_j$ of the label space, scan $s\in K$ for which
$$ p\bigl(b+u v_j+(t_i+us)a\bigr)=0\quad\text{for all }u\in K .$$
Since the univariate degree is less than $|K|$, this detects an identically zero polynomial. As the factor list is split, this happens exactly when a linear factor vanishes identically on the displayed line. At $u=0$ only factor $i$ vanishes, so the unique passing $s$ is $-\ell_i(v_j)/\ell_i(a)$. Normalizing these slopes gives the factor coefficient vector in $F$. Finally obtain $c$ using $p(a)$ and the recovered factors. Pfaffians can be evaluated by alternating elimination with field operations. The univariate scans, interpolation, and linear algebra therefore have polynomial cost. In degree zero the coefficient is the constant Pfaffian and the list is empty.

## 3. Finite harmonic projection

Let $A$ be the linear map $F^N\to(F^r)^*$ sending the $i$-th basis vector to $\ell_i$. Define
$$ R=\ker A,\qquad U=\{(\ell_i(z))_{i=1}^N:z\in F^r\}=R^\perp,\qquad a=\operatorname{rank} A .$$
The evaluation map has fibres of size $3^{r-a}$. Let $f_i(x)=\chi(x)$ for odd $e_i$ and $f_i(x)=1_{x\ne0}$ for even $e_i$. Then $I(p)=\chi(c)3^{r-a}\sum_{x\in U}\prod_i f_i(x_i)$.

Put $\omega=\exp(2\pi \mathrm{i}/3)$ and $t_{\rm tot}=\dim R$. The finite character-mean identity gives
$$
 1_U(x)=3^{-t_{\rm tot}}\sum_{y\in R}\omega^{y\cdot x}.
$$
For $x\notin U$, some nontrivial character value occurs and translation by its argument multiplies the sum by that value while preserving the sum. This proves cancellation. For $x\in U$ each summand is one. Expanding the resulting signed sum coordinate by coordinate gives
$$
 I(p)=\chi(c)\,3^{r-a-t_{\rm tot}}
 \sum_{y\in R}\prod_i\left(\sum_{x_i\in F}f_i(x_i)\omega^{y_i x_i}\right).
$$
For odd $e_i$, the inner factor equals $(\omega-\omega^2)\chi(y_i)$. For even $e_i$, it is $2$ at $y_i=0$ and $-1$ otherwise. Let $o$ be the number of odd exponents. Since $d$ is even, $o$ is even. Define integer functions $g_i=\chi$ for the odd indices and $g_i(0)=2$, $g_i(1)=g_i(-1)=-1$ for the others. The computation is therefore entirely exact over the integers:
$$
 I(p)=\chi(c)\,3^{r-a-t_{\rm tot}}(-3)^{o/2}
 \sum_{y\in R}\prod_i g_i(y_i).
 \tag{1}
$$
A negative power of three is handled by exact integer division at the end. The divisor and all numerators have polynomial bit length. The field Fourier symbols only justify the identity and need not be evaluated numerically.

Choose a basis from the $\ell_i$. Join the index of each nonbasis factor to every basis index with a nonzero coefficient in its basis expansion. This undirected graph has the matroid components as its components. Its spanning joins are the fundamental circuits. Every resulting component is connected by circuits, and the spans of different components form a direct sum because they use disjoint parts of the chosen basis. Thus no further circuit can cross them. Compute a relation basis separately on each component. Because $R$ is their direct sum, the weighted sum in (1) factors as a product of independent sums, each enumerable in $3^{t_j}\operatorname{poly}(L)$, where $t_j$ is that component's nullity. Normalizing factor vectors changes their coordinates but does not change their represented matroid or these nullities. Recognizing the bound on $t$ uses just rank tests. Requiring the target bound to be no larger than the source bound is safe on ordinarily isomorphic pairs. Each intermediate sum and product has bit length $O(N+r)$ up to fixed constants. This proves the stated complexity.

### Optional cut tree evaluation

For a supplied binary tree on the factor indices, let $J$ be the leaf set of a node and
$$ V_J=\operatorname{span}\{\ell_i:i\in J\}\cap\operatorname{span}\{\ell_i:i\notin J\} .$$
Keep at that node the weighted count of assignments whose partial sum $\sum_{i\in J} y_i\ell_i$ has a given value in $V_J$. At a leaf enumerate $y_i\in F$. At a parent add the two child partial sums and multiply the associated counts, retaining results in $V_J$. Any assignment that can contribute at a parent boundary has its restriction at each child boundary, since the negative child sum is the sum on the sibling and a sum of coordinates outside the parent. Conversely two enumerated child assignments combine to exactly one assignment at the parent. This proves induction and exact cancellation closes at zero at the root. If all cut dimensions are at most $w$, the cost is $3^{2w}\operatorname{poly}(L)$. This is an evaluation bound once the tree is supplied.

## 4. A family outside the bounded circuit bank

Fix $m\ge1$, let $N=6m$, and define a relation space $R\subset F^N$ from a rank-two matrix whose three column groups are $(1,0),(0,1),(1,1)$, each repeated $2m$ times. Take the label space $U=R^\perp$, and let $\ell_i$ be the restriction of the $i$-th coordinate functional to $U$. The least nonzero relation support size is $4m$, so the factors are nonzero and pairwise nonproportional. The three minimal relation supports are the three unions of two column groups. They overlap and connect all the factors. Thus this component has nullity two, every circuit has size $4m$, and a fixed bounded-size circuit bank eventually contains none.

With each exponent one, the only full-support nonzero elements of $R$ are the two vectors obtained by taking $a=b=\pm1$ as the row coefficients. Their values on the three blocks are $(a,a,-a)$. Their products of signs are both one, because all three block lengths are even. The weighted sum on $R$ is two, and the imbalance for the product polynomial on $U$ is exactly $2(-3)^{3m}/9$.

Realize the factors by the alternating pencil on $F^N\oplus F^N$
$$ M(z,B)=
 \begin{pmatrix}0&D(z)\\-D(z)&B\end{pmatrix},
 \qquad D(z)=\operatorname{diag}(\ell_1(z),\ldots,\ell_N(z)),
 $$
with independent label coordinates for every alternating $N\times N$ matrix $B$. Every Pfaffian matching pairs each vertex of the first block to its matching vertex of the second block, so the Pfaffian is $\pm\prod_i\ell_i(z)$. The free $B$ coordinates multiply the imbalance by a positive power of three. The pencil is concise, since the coordinate functionals span the label dual and the independent $B$ slices have disjoint support from the diagonal block. There is an invertible slice by taking each column group exactly half $1$ and half $-1$, which gives an allowed label vector in $U$ with no zero coordinate.

For the right multiplier claim let a potential multiplier have blocks $(P,Q;R',S)$. The pure $B$ coordinates show $BR'=0$ and $BS$ alternating for every alternating $B$. Taking elementary alternating matrices forces $R'=0$. The same matrices, applied to $BS$, force the rows $i,j$ of $S$ to vanish off their two columns and force $S_{ij}=S_{ji}=0$ and $S_{ii}=S_{jj}$. Thus $S=sI$. With $B=0$, comparing the two off-diagonal blocks gives $D(z)P=sD(z)$, so $P=sI$. The remaining block requires $D(z)Q$ alternating. Its diagonal gives $Q_{ii}=0$, and for $i\ne j$ the equation $\ell_iQ_{ij}=-\ell_jQ_{ji}$ gives both entries zero by nonproportionality. The multiplier space is exactly the scalar line. The assumptions survive arbitrary raw rebasings by the transporter calculation.

One can place arbitrarily many of these arrangements on disjoint factor sets before forming the same block pencil. The relation nullity of the whole arrangement can then grow while each component still has nullity two and nonzero imbalance. A negative determinant change in just the first mode produces a comparison accepted at level $P_2$ on the other two modes and rejected at level $P_3$. Thus the reduction enforces a genuine sign constraint on this family.

## Scope

The theorem is a written sufficient reduction on its stated Pfaffian family. The unrestricted $P_3\to P_2$ reduction remains open. The finite replay checks the harmonic identity and the large-circuit controls. An optional Lean companion isolates the three cube-root weight calculations in the Fourier step.
