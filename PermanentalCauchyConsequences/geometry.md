# Counterexamples and extra components in the permanent's singular locus

**Theorems.** The proposed row-or-column bipartition description in Conjecture 4.27 of Boralevi, Carlini, Michałek and Ventura fails over the reals and the complexes in exactly the sizes $n\geq 4$. Counterexamples exist with entries in $\{0,1\}$ for every such size and, for every size at least six, with every square minor nonzero. For size $n\geq2$ nonnegative real matrices outside the proposed union, the minimum permanental rank is $\lceil 2(n-1)/3\rceil$. The critical scheme is nonequidimensional in every size $n\geq 4$ in characteristic different from two. Explicit linear components have codimensions $2n+pq$ for all $p+q=n-2$.

In the conjecture, the left-hand zero locus consists of matrices with every $(n-1)$-subpermanent zero, since these subpermanents are the first derivatives of the permanent and row expansion puts the permanent in the derivative ideal. Its proposed right-hand zero locus is the union over row and column bipartitions of the loci where both blocks have all maximal subpermanents zero. The separate result that the whole singular locus has codimension $2n$ is due to Ying Xie. [Conjecture 4.27 and Remark 4.28](https://arxiv.org/html/2402.17839v2#S4.SS5) [Xie, Theorem 1.1 and Corollary 1.2](https://arxiv.org/html/2609.27320v1#S1)

## Exact ambient refutation and nonnegative rank

For integers $p,q\geq 0$ with $k=p+q\leq n$, fix a set $R$ of $p$ rows and a set $C$ of $q$ columns. Put a one at $(i,j)$ precisely when $i\in R$ or $j\in C$. Every matching in the support graph uses a distinct member of $R\sqcup C$ for each edge, so its size is at most $k$. A matching of size $k$ matches the $p$ members of $R$ to distinct columns outside $C$ and matches $q$ rows outside $R$ to the members of $C$. For nonnegative real matrices, the permanental rank equals the maximum matching size.

A block of rows has a nonzero maximal subpermanent exactly when it contains at most $q$ rows outside $R$. Those rows can be matched into $C$, and the remaining rows belong to $R$ and can be matched to unused columns. Hence a bipartition into two deficient row blocks exists exactly when $n-p\geq 2(q+1)$. The column criterion is $n-q\geq 2(p+1)$. Take $p,q\geq 1$ with $p+q=n-2$. The full matrix is critical and both criteria fail. This gives a rational counterexample in every size $n\geq 4$. Over any infinite field, assign generic weights to the supported entries. Each subpermanent with a matching is a nonzero polynomial because its matchings are distinct monomials with coefficient one. The product of all these polynomials is nonzero and thus has a nonvanishing evaluation over the field. The same sizes therefore fail over infinite fields of any characteristic.

In size three, every $2\times2$ subpermanent of a critical matrix vanishes. A zero row or column gives a deficient singleton, and its complementary block is deficient by criticality. Suppose every row and column has a nonzero entry. Any two rows must have the same support: a column occurring in only one row, together with a nonzero entry from the other row, gives a nonzero $2\times2$ permanent. Consequently every entry is nonzero. The ratios of corresponding entries for any two rows must sum to zero in every pair of columns, which is impossible for three columns in characteristic different from two. In size two the critical matrix is zero.

For the sharp nonnegative rank bound, start with any nonnegative real $n\times n$ matrix of permanental rank $k$ outside the proposed union. By Kőnig's theorem its support graph admits a minimum vertex cover with $p$ rows and $q$ columns and $p+q=k$. Any $q+1$ rows outside the cover rows are deficient, so $n-p\leq 2q+1$. Otherwise two disjoint deficient sets could be placed on opposite sides of a row bipartition. Similarly $n-q\leq 2p+1$. Adding gives $2n-2\leq 3k$. Conversely at $k=\lceil 2(n-1)/3\rceil$ choose $p+q=k$ with both $p,q\geq n-k-1$, possible by $3k\geq 2n-2$. The support construction attains that rank and avoids all the proposed partition loci. When $n\geq4$, $k\leq n-2$, so the bound is sharp among singular counterexamples as well.

## Linear components of different dimensions

Work over an algebraically closed field of characteristic different from two. Fix $p+q=n-2$, allowing one of $p,q$ to be zero. Let $L_{R,C}$ be the coordinate plane supported on rows $R$ and columns $C$. Matching support proves that $L_{R,C}$ lies in the critical scheme. The number of forced zeros is $(q+2)(p+2)=2n+pq$.

Index the equations by the deleted row $i$ and column $j$ in an $(n-1)$-subpermanent. Its derivative in entry $(r,c)$ is zero if $i=r$ or $j=c$. Otherwise it is the permanent after deleting both rows and both columns. On $L_{R,C}$ this permanent is zero unless the retained submatrix contains all $p$ rows of $R$ and all $q$ columns of $C$, because a matching needs $n-2=p+q$ members of the cover. The only potentially nonzero Jacobian entries have $i,r$ outside $R$ and $j,c$ outside $C$.

When $i\neq r$ and $j\neq c$, all $q$ retained rows outside $R$ must be matched to columns in $C$, and all $p$ retained columns outside $C$ must be matched to rows in $R$. The derivative factors as $U_{ir}V_{jc}$, where $U$ and $V$ are symmetric matrices of complementary permanents of the two rectangular blocks, with zero diagonal. The Jacobian block equals $U\otimes V$ after ordering index pairs. The two rectangular blocks can be assigned independently.

For a rectangular block of size $d\times(d+2)$, transposing if necessary, specialize it to $[I_d\mid\mathbf 1\mid\mathbf 1]$. Its complementary-permanent matrix becomes
$$
\begin{pmatrix}
2(J_d-I_d)&\mathbf1&\mathbf1\\
\mathbf1^{\mathsf T}&0&1\\
\mathbf1^{\mathsf T}&1&0
\end{pmatrix}.
$$
Deleting two identity columns leaves two bijections from the added columns to the unused identity rows. Deleting an identity column and an added column leaves exactly one bijection. Deleting both added columns gives permanent one. Here $J_d$ is the all-ones matrix. The Schur complement of the bottom-right block is $-2I_d$, so the determinant is $-(-2)^d\neq 0$, including $d=0$ by the empty-matrix convention. These assignments make the entire Jacobian block invertible.

The tangent space of the critical scheme at this point has dimension exactly $n^2-(q+2)(p+2)$, the dimension of $L_{R,C}$. The local dimension is at least this large because it contains the plane and at most this large by the tangent bound. Equality makes the point smooth and puts it on a unique component. The closed irreducible plane has the same dimension as that component, hence is the whole component and is smooth on a dense open subset. The choices $p=0$ and $p,q\geq 1$ give components of different dimensions for every $n\geq4$. For $p,q\geq1$ generic points on the plane also avoid the proposed union by the matching-witness polynomial argument. Nonequidimensionality in size four was already observed by Landsberg. [Landsberg, *Geometry and Complexity Theory*, Section 6.3.2](https://people.tamu.edu/~jml/simons662.pdf)

## A totally nonsingular real witness in size six

Define
$$
\begin{aligned}
A(z)&=(z^2-1)(z^4-3z^2+1)=z^6-4z^4+4z^2-1,\\
B(z)&=(z^2-2)(z^4-7z^2+4)=z^6-9z^4+18z^2-8,\\
H_1(z)&=z^4+7z^2+1,\qquad H_2(z)=z^3+z.
\end{aligned}
$$
The roots of $A$ and $B$ are real and simple. As polynomials in $u=z^2$, their root sets are respectively $\{1,(3-\sqrt{5})/2,(3+\sqrt{5})/2\}$ and $\{2,(7-\sqrt{33})/2,(7+\sqrt{33})/2\}$, each with three distinct positive elements. The two sets are disjoint. Substitution excludes common roots $1$ and $2$, and a common root of the two quadratics would be $3/4$ by subtraction, which fails the first quadratic.

Let $a_1,\ldots,a_6$ be the roots of $A$ and $b_1,\ldots,b_6$ the roots of $B$. Set $M_{ij}=1/(b_j-a_i)$. In every square submatrix of order $k$, a dependence among rows would give a sum of simple fractions in $k$ distinct poles vanishing at $k$ distinct evaluation points. The numerator has degree at most $k-1$, so it vanishes identically. Its evaluations at the poles imply all dependence coefficients are zero.

The two exact polynomial identities are
$$
A'(BH_\nu)'-A''BH_\nu=A R_\nu\qquad(\nu=1,2),
$$
where
$$
\begin{aligned}
R_1(z)&=30z^8-28z^6-264z^4+432z^2-64,\\
R_2(z)&=24z^7-96z^5+96z^3.
\end{aligned}
$$
They follow by expansion. For either $P=BH_\nu$, the coefficient of $(z-a_i)^{-1}$ in $P(z)/A(z)^2$ is
$$
\frac{A'(a_i)P'(a_i)-A''(a_i)P(a_i)}{A'(a_i)^3}=0.
$$
Indeed $A(z)=(z-a_i)A_i(z)$, where $A_i(a_i)=A'(a_i)$ and $2A_i'(a_i)=A''(a_i)$, and the coefficient is the derivative of $P/A_i^2$ evaluated at $a_i$. The rational function is proper, so its partial fractions are exactly
$$
\frac{B(z)H_\nu(z)}{A(z)^2}
=\sum_{i=1}^6\frac{c_{\nu i}}{(z-a_i)^2},\qquad
c_{\nu i}=\frac{B(a_i)H_\nu(a_i)}{A'(a_i)^2}.
$$
The two coefficient vectors are linearly independent, since a linear combination with all coefficients zero would give the corresponding linear combination of the independent polynomials $BH_1,BH_2$ equal to zero. Evaluation at each $b_j$ shows that both kill $M^{\circ2}$ from the left. Hence $\operatorname{rank}(M^{\circ2})\leq 4$.

On each square Cauchy submatrix $C$, Borchardt's identity gives $\det(C^{\circ2})=\det(C)\operatorname{per}(C)$. Thus all subpermanents of order five vanish. In contrast, any fixed set of $r$ rows with $1\leq r\leq 3$ has independent rows in $M^{\circ2}$, because a linear combination vanishing on all six column parameters would have a numerator of degree at most $2r-2<6$. The numerator must vanish identically, and evaluation at the poles gives zero coefficients. Some $r\times r$ minor of those squared rows is nonzero, so the corresponding submatrix of $M$ has nonzero permanent. The argument interchanges rows and columns. Taking a smaller side of each bipartition proves the stated property for $M$. The size-six witness is minimal within square Cauchy matrices over characteristic zero by the [companion Cauchy defect bound](algebra.md#2-a-wronskian-bound-in-characteristic-zero-and-large-characteristic). [Borchardt's identity, Lemma 2.1](https://www.kurims.kyoto-u.ac.jp/~kyodo/kokyuroku/contents/pdf/1913-06.pdf)

## A sparse extension by identity blocks

Take $X=M\oplus I_{n-6}$. A square submatrix of a block diagonal matrix has permanent zero if the row and column counts disagree in any diagonal block. When the counts agree, its permanent is the product of the selected diagonal subpermanents. Thus nonzero subpermanents of $X$ have order at most $4+(n-6)=n-2$. Here the order-six permanent of $M$ is also zero, by the same Borchardt identity and rank bound.

In a bipartition of the rows, choose a side containing between one and three rows from $M$ if both sides meet its six rows. That side has a nonzero maximal subpermanent by the size-six property, using the matching identity columns for all its other rows. If only one side meets the six rows, the other side consists of identity rows and has a nonzero maximal subpermanent. The same proof applies to columns. This completes the counterexample for every $n\geq 6$. The block extension preserves the size-six construction in all larger sizes.

## Totally nonsingular Cauchy counterexamples in every size at least six

Write $K_{ij}=(b_j-a_i)^{-2}$ and let all $a,b$ vary in the real open set of pairwise disjoint, distinct parameters. Near a matrix of rank exactly $n-2$, choose an invertible $(n-2)\times(n-2)$ minor. The rank condition is locally the vanishing of the four entries of its $2\times2$ Schur complement. Its differential in a direction $\delta K$ is $U(\delta K)V$, where $U$ and $V$ are the left and right nullspace bases of $K$ normalized to have identity blocks on the complementary indices. This follows by differentiating $D-CP^{-1}Q$ at $K=\left(\begin{smallmatrix}P&Q\\C&D\end{smallmatrix}\right)$, which gives $U=(-CP^{-1},I)$ and $V=\left(\begin{smallmatrix}-P^{-1}Q\\I\end{smallmatrix}\right)$.

For the size-six witness, order the real $a$-parameters as $(1,\phi^{-1},\phi,-\phi,-\phi^{-1},-1)$, where $\phi=(1+\sqrt{5})/2$. Order the $b$-parameters as $((\sqrt{3}-\sqrt{11})/2,(\sqrt{3}+\sqrt{11})/2,\sqrt{2},-\sqrt{2},-(\sqrt{3}+\sqrt{11})/2,-(\sqrt{3}-\sqrt{11})/2)$. The radical field is multiquadratic, with independent squareclasses $2,3,5,11$, so in the subring generated by these radicals over $\mathbb Z[1/2]$ one can reduce modulo $239$ by sending the four radicals to $99,133,31,49$, respectively. Their squares give the required radicands modulo $239$. The parameters reduce to $(1,15,16,223,224,238)$ and $(42,91,99,140,148,197)$, which are disjoint and have no repetitions. Thus localizing at the differences preserves this reduction.

The determinant of the leading $4\times4$ block of $K$ is $200$ modulo $239$. Therefore $K$ has real rank exactly four, and its normalized nullspace bases reduce to the following vectors listed as rows:
$$
\begin{aligned}
U&: (21,236,214,88,1,0),\quad (3,11,12,0,0,1),\\
V&: (33,94,150,120,1,0),\quad (145,232,163,119,0,1).
\end{aligned}
$$
These modular vectors are verified by multiplication and by the two identity blocks. The derivative with respect to $a_i$, divided by two, is zero outside row $i$ and has row entries $(b_j-a_i)^{-3}$. In lexicographic order of the four coordinates of $U(\delta K)V$, the derivative with respect to $(a_1,a_2,a_3,a_4)$, after this division, reduces to
$$
\begin{pmatrix}
58&220&222&71\\
119&121&178&39\\
179&229&142&0\\
17&114&144&0
\end{pmatrix}.
$$
Its determinant is $103$ modulo $239$. Both nullspace bases, the leading minor and this determinant were independently recomputed with exact modular arithmetic. The real derivative in these four parameters is therefore invertible.

Suppose size $n$ has such a rank-$n-2$ point where the four Schur-complement coordinates have an invertible derivative in four old parameters. Adjoin a new row node $a_*$ outside all the old nodes and a new column node $a_*+t$. For $t\neq0$ the new corner is $t^{-2}$. Eliminating that pivot leaves the old matrix $K$ minus $t^2$ times the outer product of the off-diagonal column and row. This Schur complement extends real analytically to $t=0$ and is $K$ there. The old pivot minor in this complement remains invertible nearby. Its four residual Schur-complement entries have the same invertible derivative in the four selected old parameters at $t=0$. The implicit function theorem varies those four parameters as functions of $t$ so the four entries stay zero. The derivative remains invertible by continuity. For small nonzero $t$ the larger squared Cauchy matrix then has rank exactly $1+(n-2)=(n+1)-2$. Successive elimination of the new corner and the old pivot block is elimination of their combined invertible pivot block, so the derivative gives the same rank-coordinate property for the next induction step. All nodes are distinct and disjoint for sufficiently small nonzero $t$.

Thus in every size $n\geq6$ there is a real Cauchy matrix with squared-entry rank exactly $n-2$. Borchardt's identity gives vanishing of all $(n-1)$-subpermanents. For each side of size $r\leq\lfloor n/2\rfloor$, the degree argument for squared Cauchy slices gives full squared rank since $2r-2<n$. Each row or column bipartition has such a side, which has a nonzero maximal subpermanent. All ordinary square minors are nonzero by the simple-fraction argument.

**Verification.** The geometric and combinatorial arguments are informal proofs. The two displayed polynomial identities for the size-six witness were checked by Lean as exact rational identities.
