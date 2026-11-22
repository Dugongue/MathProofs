# Exact coefficient-size tests for the square-zero slice pencils

Use the displayed common parameter coordinates of the square-zero pencils in the small matrix substitution construction. Let $k$ be a field, let $h\ge2$, and set $m=h+1$. For original matrix spaces $M,M'\subseteq\operatorname{Hom}_k(k^a,k^b)$ of a matched format, define
$$
 d_*=\min\{\operatorname{rk}A:A\in M\triangle M'\},\qquad t=md_* .
$$
If the spaces agree, all the compared evaluations agree up to the respective equivalences at every size. Below take $M\ne M'$. Over a finite commutative chain ring use the same definition over its residue field, and lift the pencil at a fixed nonzero socle element $s$. [Starting square-zero pencil](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md)

**Theorem.**

1. The first unrestricted coefficient size that can distinguish a pair is exactly $t$. Below this size every substitution gives the same rational canonical form over a field and the same Smith form for every scalar polynomial in the evaluation over a finite chain ring. This applies both to the ordinary pencil and to the normalized symmetric pencil. At size $t$ a centered substitution already distinguishes by rank or Smith form.
2. If all coefficient matrices, including the scalar coefficient matrix, are symmetric, the first size is either $t$ or $t+1$. This holds in every residue characteristic for congruence of the actual symmetric evaluations and separately for rational canonical forms or polynomial Smith forms of the normalized evaluations. The first size is exactly $t+1$ if
   $$
   \max\left\{
   \dim\operatorname{span}\{A\in M\colon\operatorname{rk}A\le d_*\},
   \dim\operatorname{span}\{A\in M':\operatorname{rk}A\le d_*\}
   \right\}<t .
   \tag{1}
   $$
   The threshold is also exactly $t+1$ for every pair with $d_*=1$. In particular, $M=kA$ and $M'=0$ attain $t+1$ for every nonzero $A$.
3. A specified nonzero $A$ of rank $r$ can be tested for membership in $M$ by a single explicit centered substitution. The exact worst-case coefficient size for this test is $mr$ with unrestricted coefficients and $mr+1$ with symmetric coefficients. At constant $h$, deciding whether a pair has a distinguishing substitution of size at most a given bound is NP-complete for binary input matrix spaces in either coefficient model.

Thus unrestricted transcripts through size $q$ determine exactly marked rank-truncated data through rank $\lfloor q/m\rfloor$. For symmetric transcripts the same exact classification holds whenever $q$ is not divisible by $m$, since each such rank has its one-extra-index witness within size $q$. At sizes divisible by $m$, the possible gap affects only the highest rank layer. The costs in part 3 refer to information from substitution signatures.

The lower bounds are for each matched coefficient substitution, including ones with nonzero scalar coefficient and noncommuting matrix coefficients. They do not assume that an observed matrix preserves the displayed coordinates. The symmetric congruence lower bounds also give determinant-one congruences.

## 1. Compression to a centered rectangular matrix

Write $d=a+b$, $Z=k^a\oplus k^b$, and let $\widetilde A$ take $k^a$ into $k^b$ by $A$ and kill $k^b$. The quadratic relation space $H_M\subseteq\operatorname{Sym}^2 V$ is the span of
$$
 q_B=x^{\mathsf T}B^{\oplus m}y,\qquad
 B=[\xi I_Z+\widetilde A,\ \zeta I_Z],
 \quad A\in M,\ \xi,\zeta\in k .
$$
Here the full direction space $V$ also has the common inert direction of the starting pencil. When $(\xi,\zeta)\ne(0,0)$, $B$ has rank $d$. Otherwise its rank is $\operatorname{rk} A$. The polar matrix of $q_B$ has rank $2m\operatorname{rk}B$ in every characteristic. The centered blocks are $v\mapsto s[uv]$, where the quotient is by $H_M$, with field coordinates identified with $sR$ and with the original inert padding in $W$. Take $s=1$ over a field.

For coefficient size $q$, let $Y$ be the scalar coefficient matrix and $U=(u_{ij})$ be the corresponding $q\times q$ direction array. Grouping the square-mode space as $V^q\oplus W^q$, the evaluation is
$$
 E_M(Y,U)=
 \begin{pmatrix}
 Y\otimes I_V&0\\ s D_M(U)&Y\otimes I_W
 \end{pmatrix},
 \qquad
 D_M(U)(v_1,\ldots,v_q)_i=\Big[\sum_j u_{ij}v_j\Big].
 \tag{2}
$$
For a ring this notation uses the residue directions and a coefficientwise lift before multiplying by $s$.

Over a field, use independent row and column maps to reduce $Y$ to a diagonal with ones and zeros. Over a chain ring use Smith reduction. Whenever a diagonal entry is nonzero, it divides $s$ over the chain ring and is invertible over a field. Eliminate all $sD_M$-blocks incident to a nonzero scalar row using the $W$ columns, and all remaining blocks incident to a nonzero scalar column using the $V$ rows. The eliminating maps are block shears of determinant one and leave the complementary zero-by-zero block untouched. The result is the common scalar part and one residual centered matrix, obtained by compressing the coefficient directions to the left and right zero slots of the scalar Smith reduction. The Smith form of that residual centered matrix depends only on its residue rank: it has one copy of $s$, up to associates, per unit pivot of that residue map. Over a field the same statement is ordinary rank. Thus the rank or Smith form in (2) is fixed by the scalar data and the centered residue rank of a substitution of size at most $q$.

For symmetric $Y$ and symmetric $U$, the surviving centered residue directions can be chosen symmetric. Over a field this is restriction to a common basis of $\ker Y$ on both sides. Over a chain ring the residue span of the free zero slots on either side is the image of $\ker Y$ in $k^q$. Indeed in Smith coordinates every coordinate killed by a nonzero diagonal entry reduces to zero, and coordinates at zero entries are unrestricted. The two sides give bases of the same subspace because $Y^{\mathsf T}=Y$. Changing to the same residue basis on both sides preserves the centered rank. This argument works even for a symmetric alternating scalar block in characteristic two.

For any scalar polynomial $f$, $f(E_M(Y,U))$ has the same shape with scalar coefficient $f(Y)$. The new direction array is obtained from the terms with one centered factor. For $f(X)=X^j$, their array is $\sum_{i=0}^{j-1}Y^i U Y^{j-1-i}$. All terms with two centered factors vanish. The formula is independent of the carrier and, if $Y,U$ are symmetric, the new array is symmetric because transposition pairs summands. Thus a lower bound for all centered ranks at a coefficient size implies agreement of all polynomial ranks or Smith forms at that size. Over a field the nullities of powers of irreducible polynomials determine the elementary divisors.

The normalized symmetric evaluation with unrestricted coefficient matrices is the direct sum of (2), the transpose of (2) formed with **transposed coefficient matrices**, and the common optional scalar block. With symmetric coefficients the actual symmetric evaluation is
$$
 \begin{pmatrix}0&E_M(Y,U)^{\mathsf T}\\ E_M(Y,U)&0\end{pmatrix}
$$
together with that common block. Left-right equivalence of $E_M,E_{M'}$ therefore gives congruence. These congruence witnesses can have determinant one. If there are no zero scalar slots, the elimination of the two centered parts used only shears and a common scalar reduction. If there is a zero slot, its inert $W$-coordinate gives a zero row of the reduced evaluation. Scaling this row by an arbitrary unit corrects the determinant of the resulting left-right witness without changing its equation. The induced congruence has determinant the product of the two left-right determinants. Conversely a rank or Smith difference in $E_M,E_{M'}$ changes the rank or multiplicities of nonzero Smith factors of the symmetric evaluation, since it doubles those multiplicities and adds fixed scalar factors.

## 2. Recovering a chosen relation at size $mr$

For $U_0\subseteq V$, let $U_0V$ denote the degree-two products with one factor in $U_0$. A quadratic in $U_0V$ has polar rank at most $2\dim U_0$. Thus a rank-$r$ matrix $B$ can contribute $q_B$ only to $(U_0V)$ of width at least $mr$. All nonzero anchored data matrix differences have first possible rank $d_*$: matrices with a nonzero anchor coefficient have rank $d>d_*$, and the zero-anchor parts record the symmetric difference of $M,M'$.

The following isolator from the marked subpencil argument gives a targeted upper bound. For a given nonzero rectangular matrix $B$ of rank $r$, one can compute $mr$ independent directions spanning $U_B$ with
$$
 \{C:q_C\in U_BV\}=kB .
 \tag{3}
$$
Put $B$ in supported identity form by independent row and column operations, the same in every copy. In two copies, let $x_0,y_0$ be the $2r$ supported variables of the two types. For $J_1,J_2$ take alternating matrices supported on the two disjoint matchings of the path on $r$ vertices, using successive edges of odd or even starting index. Use the directions $x_0+S y_0$ where $S=\left(\begin{smallmatrix}J_1&I\\-I&J_2\end{smallmatrix}\right)$. It is invertible since $J_2J_1$ is nilpotent, moving odd and even indices two steps toward opposite ends. In remaining copies use the pure supported $x$-variables. Modulo the ideal of these directions, the substitute $x_0=-S y_0$ first forces any surviving $C$ to have zero unsupported rows and columns. On its active square block $C_0$ the vanishing condition is that $S\operatorname{diag}(C_0,C_0)$ be alternating. The identity blocks make $C_0$ symmetric and the diagonal blocks impose commutation with $J_1,J_2$ and zero diagonals of $J_i C_0$. A commuting map is specified by the image of the first vertex, then by propagation along the path edges. For odd $r$ the first vertex spans $\ker J_2$, giving scalars. For even $r$ that kernel is the two endpoints. In addition to scalars the possible map is the signed reversal, which produces a nonzero diagonal at the middle matched edge in $J_iC_0$. It is therefore excluded in every characteristic. Scalars satisfy the required equations. [Two-copy isolation and marked width](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Algorithms.md)

If a centered array has size $q<t$, every row direction span has dimension at most $q$, and in its product space the intersections with $H_M,H_{M'}$ agree. Indeed a discordant relation would have polar rank at least $2t$. It follows row by row that
$$
 \ker D_M(U)=\ker D_{M'}(U).
$$
This gives equal ranks for all centered substitutions below $t$, and Section 1 handles all scalar coefficients and polynomials. For size $t$, take a minimal-rank discordant $A$, use its zero-anchor $B$, and place the $t$ basis directions of (3) in a single block row, all other rows zero. Its rank is $\dim U_BV-1$ on the side containing $A$, and $\dim U_BV$ on the other side. For the additional transpose portion of the normalized symmetric pencil, the transposed direction array has a single nonzero block column. Its rank is $D=\dim V$ on both sides since $\beta(u,-)$ is injective for a nonzero direction $u$. Thus the difference survives in either normalized pencil. Exactly the same construction tests any supplied rank-$r$ matrix for membership, with size $mr$.

With symmetric coefficients, use one extra index. Put the $mr$ directions along the edges of a star from this extra index, with equal labels in its row and column, and put zero on all diagonals. The rows at the leaves force the vector at the center to vanish when evaluating a centered kernel, by injectivity of any nonzero $\beta(u,-)$. The remaining kernel equation, at the center, is the same as the single-row equation above. This gives the asserted size $mr+1$ for membership and distinguishes the pair at size $t+1$. The separating centered coefficient arrays lift to every finite local ring in the original construction. The orders of their images differ by a factor of $|k|$ in the ordinary case or $|k|^2$ when doubled with symmetric coefficients in the symmetric case.

## 3. The boundary for symmetric coefficients

Fix a symmetric centered array of size $q=t$. If $D_M$ and $D_{M'}$ have different kernels, one side has a kernel vector $\mathbf v=(v_1,\ldots,v_t)$ giving row quadrics $Q_i=\sum_j u_{ij}v_j\in H_M$ with at least one discordant row. Write $L=\operatorname{span}(v_j)$. A discordant row has polar rank $2t$, because it is at least $2t$ by $d_*$ and at most $2\dim L$ by membership in $LV$. Hence the $v_j$ are independent. The cross block of that row quadric from $L$ to $V/L$ has rank $t$. In fact its full polar matrix has shape $\left(\begin{smallmatrix}A&B\\B^{\mathsf T}&0\end{smallmatrix}\right)$ and rank at most $t+\operatorname{rk}B$.

All $t$ row quadrics must be linearly independent. Suppose $\sum_i\lambda_i Q_i=0$. Modulo $\operatorname{Sym}^2 L$ in $LV$, comparison of coefficients of the basis $v_j$ gives $\sum_i\lambda_i\bar u_{ij}=0$ for every $j$, with bars in $V/L$. By symmetry this is also $\sum_j\lambda_j\bar u_{ij}=0$ for every $i$. At the discordant row the cross block has rank $t$, forcing $\lambda=0$.

Every row relation has polar rank at most $2t$. No such row can involve an anchor, since $d>d_*$. Thus the $t$ independent row quadrics come from $t$ independent data matrices of rank at most $d_*$ on one side. Condition (1) rules this out. The smaller compressed centered arrays are already covered by Section 2. Therefore Section 1 proves agreement for **every** symmetric coefficient substitution and separately for every scalar polynomial of its normalized evaluation through size $t$. Together with the star witness this gives exact size $t+1$ under (1), including the one-line versus zero comparison. The equality of all polynomial ranks or Smith forms is derived directly from the centered reduction and does not rely on congruence implying similarity.

There is an unconditional improvement when $d_*=1$, even if (1) fails. Suppose a discrepant kernel at $q=t=m$ exists. By the preceding argument all $m$ row quadrics are nonzero and linearly independent. They have polar rank $2m$, so each is a repeated rank-one quadratic with zero anchors.

For each row, the image in $V$ of its polar matrix contains $L$. Indeed the cross block has rank $m$, so contraction against functionals annihilating $L$ maps onto $L$. A rank-one repeated quadratic has polar image $X_\ell\oplus Y_\ell$, where $X_\ell$ is the sum of the $m$ copies of one line in the left factor and $Y_\ell$ is the sum of the $m$ copies of one line in the right factor. Take any two of the independent row quadrics. Their left and right factor lines cannot both agree, since that would make the quadrics proportional. If neither factor line agreed, the two polar images would have zero intersection. Because both contain $L$, precisely one factor line agrees, and the intersection is its pure repeated factor. It has dimension $m$ and equals $L$. Every other row shares that same factor, since its polar image also contains $L$.

Choose the new input list $v'_j$ to be the copy-$j$ vector of this common pure factor, using the same base vector in all copies. This is a change of coefficient basis. In column notation take $v'=P^{-\mathsf T}v$ and $U'=PUP^{\mathsf T}$, where $P\in\mathrm{GL}_m(k)$ is selected to give the desired list. The new rows of quadrics are $Q'=PQ$, and $U'$ is symmetric. These row quadrics remain independent and nonzero. They lie in $LV$ and still have polar rank at most $2m$, so they again have rank-one zero-anchor data. Thus they also share the pure factor $L$.

The new row $Q'_i$ is a sum over copies of the fixed pure factor times one repeated opposite factor. In the basis $v'_j$, its cross coefficient $\bar u'_{ij}$ in $V/L$ is the copy-$j$ vector of that opposite factor. For $i\ne j$, the equality $\bar u'_{ij}=\bar u'_{ji}$ makes both zero, since the two opposite copy spaces are disjoint. For every row $i$ there is a $j\ne i$, so its repeated opposite factor vanishes and $Q'_i=0$. This contradicts independence. The compression of Section 1 then gives agreement through size $m$ for every symmetric coefficient substitution and every polynomial signature, and the star gives the exact threshold $m+1$.

For a general pair the boundary can be written as an explicit zero-scalar kernel criterion. For symmetric $U$ define $P_U:V^t\to(\operatorname{Sym}^2 V)^t$ by the unquotiented row products. Size $t$ distinguishes exactly when some such array satisfies
$$
 \dim\big(\operatorname{im}P_U\cap H_M^t\big)\ne
 \dim\big(\operatorname{im}P_U\cap H_{M'}^t\big).
$$
Both directions follow by the compression reduction and the rank formula for the composed quotient map. The criterion and condition (1) leave the boundary open for $d_*>1$ when the available low-rank relation spans are larger. The uniform membership cost remains exact, because $M=kA,M'=0$ is one of the admissible pairs.

## 4. Complexity and scope

At fixed $h$, given a binary linear code $C$, use $M=\{\operatorname{diag}(c):c\in C\}$ and $M'=0$. The first unrestricted size is $md_{\min}(C)$. The first symmetric size belongs to $\{md_{\min}(C),\,md_{\min}(C)+1\}$, so its quotient by $m$ rounded down is the same distance. Thus a minimum-distance bound $b$ maps to size bound $mb$ in the unrestricted case and $mb+1$ in the symmetric case. The next possible interval starts at $m(b+1)>mb+1$. The problem lies in NP, since a centered coefficient array of polynomial size certifies separation by two explicit rank computations; one never needs size beyond $m\min(a,b)+1$. For unrestricted substitutions a discordant matrix itself is a smaller certificate. This proves the NP-completeness claim. [Vardy, *Algorithmic complexity in coding theory and the minimum distance problem*](https://doi.org/10.1145/258533.258559)

The field results are about rational canonical forms and the actual symmetric congruence class where applicable. The polynomial Smith and congruence statements over rings use the chain-ring compression. The centered witnesses themselves apply to the broader finite local-ring construction. The coefficient matrices are marked and matched across instances. The starting theorem gives a universal width guarantee. The result here computes the sharp unrestricted size for each pair, gives symmetric recovery using just one additional index, and improves the universal symmetric small-size guarantee in characteristic two to the same $q\le h$ as in odd characteristic. Noncommutative rank studies a maximal attainable blow-up rank, whereas the bounds here concern the first discrepancy at identical coefficient values in two pencils. The proof is in prose, and this search did not establish publication priority. [Ivanyos–Qiao–Subrahmanyam](https://arxiv.org/abs/1512.03531) · [Bik–Neri, symmetric rank-metric codes](https://arxiv.org/abs/2303.06745)

## Finite controls

For $h=2$ and format $(2,2,1)$, compare a single rank-one matrix with a single rank-two matrix. The common direction dimension is $D=37$. The single-row size-three witness gives centered nonzero Smith-factor counts 107 and 108, from $\dim UV=3D-\binom32=108$. The symmetric size-four star adds $D$ on both sides, giving 144 and 145. An exact sparse-matrix check returned these counts over $\mathbb F_2,\mathbb F_3,\mathbb Z/4,\mathbb Z/9$. It also checked 48 matching polynomial signatures at symmetric size three, including zero, nonunit diagonal and alternating scalar blocks. The checks instantiate the centered maps and use the starting artifact's exact signature routine.
