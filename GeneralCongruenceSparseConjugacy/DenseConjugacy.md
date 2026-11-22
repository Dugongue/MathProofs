# Sharp cubic sparse size exponent for conjugacy with unequal traces

Over every field, among all pairs of $n$-by-$n$ matrices $A,B$ with $\operatorname{tr}A\ne\operatorname{tr}B$, the worst-case sparse Polynomial Calculus refutation size of $XA=BX$, $XY=I$, $YX=I$ is between $\Omega(n^3)$ and $O(n^3\log(2n))$. Consequently its power-law exponent is exactly three. The proof permits arbitrary degrees, ordinary commutative variables, and the original two-premise PC rules. It uses explicit integral matrices that work after reduction in every characteristic. [Original equations in Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3)

In contrast, the same gap-one idempotents in diagonal coordinates have sparse exponent two. Degree is exactly two in both presentations. Thus even the asymptotic power of the sparse size depends on the input bases, including when their changes are explicit integral unimodular shears. [Diagonal-coordinate theorem](SparseConjugacy.md)

## Upper bound for arbitrary matrices of unequal traces

The polynomial identity
$$
 \operatorname{tr}A-\operatorname{tr}B
 = \operatorname{tr}(A(I-YX))-\operatorname{tr}(B(I-XY))
   +\operatorname{tr}(Y(XA-BX))
$$
follows by cyclic invariance of trace for matrices over the commutative polynomial ring. Each term before summation is a scalar multiple of one inverse equation or one variable times a forward equation, with $O(n)$ monomials. There are $O(n^2)$ such terms. At each level of a balanced binary summation tree the total number of monomials is bounded by the total number at its leaves. This gives the stated $O(n^3\log(2n))$ size bound and degree two. Multiply the final nonzero scalar by its inverse.

## How many forward equations are indispensable?

Put $h=r+g$ with $r,g\ge1$, and take complementary idempotent ranks $h,r$ on side $n=r+h$. Allow arbitrary independent choices of bases on the source and target. **Every refutation must use at least $h(r+1)$ distinct indexed forward constraints**, counting distinct scalar equations as available input lines up to proportionality. More precisely, any subset of fewer indexed forward entries is consistent over the algebraic closure with all inverse equations. Redundancies among equal or proportional entries do not help.

To prove this, let $U_1,U_0$ be the two source eigenspaces of dimensions $h,r$, and let $V_1,V_0$ be the target spaces of dimensions $r,h$. All maps of the form
$$
 X=\begin{pmatrix} L&0\\T&M\end{pmatrix}
$$
have $XA-BX$ supported on the single map $T:U_1\to V_0$ in these eigenspace coordinates. Thus $m$ arbitrary original forward entries impose at most $m$ homogeneous linear restrictions on the $h$-by-$h$ matrix $T$. They impose no restriction on $L,M$. A linear space of $h$-square matrices of dimension greater than $h(g-1)$ over an algebraically closed field contains a matrix of rank at least $g$. This bounded-rank dimension estimate is the square case of Flanders's theorem. A proof in the form used here follows below. [Flanders, *On spaces of linear transformations with bounded rank*](https://doi.org/10.1112/jlms/s1-37.1.10)

If $m<h(r+1)$, the solution space for $T$ therefore contains such a matrix. Choose a $g$-dimensional subspace $K\subset U_1$ on which $T$ is injective. Choose $L:U_1\to V_1$ surjective with kernel $K$, and $M:U_0\to V_0$ injective with image a complement to $T(K)$. The displayed block $X$ is injective and hence invertible. Putting $Y=X^{-1}$ satisfies all inverse equations. This proves the lower bound on the number of used forward inputs.

For its exactness as an input-count bound in displayed diagonal coordinates, use all crossing entries in $r+1$ rows of $T$. Their vanishing leaves at most $g-1$ nonzero rows. For any map $X$ satisfying those equations, the image of $X$ on the $h$-dimensional subspace $U_1$ has dimension at most $r+(g-1)<h$. No invertible $X$ satisfies this subset. The corresponding polynomial system has a PC refutation by the Nullstellensatz and scalar descent, using at most these $h(r+1)$ forward inputs.

For completeness, take any linear subspace of $h$-square matrices all of rank at most $g-1$. Assign the distinct weights $h i+j$ to the entries, indexing rows and columns from zero. Row-reduce a basis of the subspace as vectors in this increasing entry order. For a basis vector with first nonzero entry of weight $b$, multiply on the left and right by the diagonal matrices with entries $t^{h i}$ and $t^j$, and divide the result by $t^b$. All entries are polynomials in $t$. At zero this matrix is a nonzero multiple of its pivot unit. For nonzero $t$ all combinations of transformed basis vectors have rank at most $g-1$, since the row and column scalings are invertible and vector-dependent scalar factors preserve the common linear space before scaling. The minors vanish at zero as well, by polynomial identity over the infinite algebraic closure. Hence the coordinate subspace on the pivots also has rank bounded by $g-1$. View its pivots as edges in a bipartite graph. A matching of size $g$ gives a rank-$g$ matrix on those edges. By the bipartite matching-cover theorem a graph with no such matching has a vertex cover of size at most $g-1$ and hence at most $h(g-1)$ edges. This bounds the original dimension.

## Integral dense presentations

Write $J_{a,b}$ for an $a$-by-$b$ all-ones matrix and abbreviate square $J_{a,a}$ to $J_a$. Use $B=\operatorname{diag}(I_r,0_h)$ and the rank-$h$ matrix
$$
A=\begin{pmatrix}
 I_h-rJ_h & J_{h,r}\\
 (1-hr)J_{r,h}&hJ_r
\end{pmatrix}.
$$
It is obtained by conjugating $\left(\begin{smallmatrix}I_h&J_{h,r}\\0&0\end{smallmatrix}\right)$ with $\left(\begin{smallmatrix}I_h&0\\J_{r,h}&I_r\end{smallmatrix}\right)$. The former matrix is itself an integral unitriangular conjugate of $\operatorname{diag}(I_h,0_r)$. Therefore $A$ remains an idempotent of rank $h$ over every field. For a column in its last $r$ positions, the first $h$ entries equal one. In a column in its first $h$ positions, all $h-1$ off-diagonal top entries are nonzero when $r$ is nonzero in the field. If $r$ vanishes there, all $r$ entries of the lower block equal one. Thus in every column there are at least $r-1$ nonzero entries off its diagonal. Each polynomial $(XA-BX)_{ij}$ has at least $r-1$ distinct nonzero monomials in the original variables, since $B$ is diagonal and its contribution only affects $X_{ij}$.

The forward-input count now forces size at least $(r-1)h(r+1)$. For gap one, $n=2r+1$ and the matrix traces differ by one in every characteristic. This yields the cubic lower bound for odd $n$. Padding both matrices by a common zero singleton block handles even $n$, since a refutation for the padded pair restricts to a proof for the old pair by putting the new row and column of both variable matrices equal to the corresponding identity row and column. No substituted monomial grows. Together with the upper bound this proves the worst-case exponent.

## A general lower bound invariant under basis changes

For arbitrary nonconjugate matrices over any field, let $r_i$ be the smaller multiplicity of a mismatched Jordan type over a splitting field, and let $\ell_i$ be the length of that type. Put $k=\min_i\lfloor r_i/\ell_i\rfloor$. A proof must use at least $k+1$ inverse entries and hence has sparse size at least $n(k+1)$. This assertion applies in arbitrary bases.

Indeed, let $U$ span the coordinate vectors for the columns of the selected $YX-I$ entries and let $V$ span those for the columns of the selected $XY-I$ entries. If each dimension is at most $k$, one can satisfy those entries and every forward equation at once. In each Jordan type let the intertwiner on that full direct summand be an arbitrary linear map between the two multiplicity spaces tensored with the identity on the chain. For equal multiplicities use an isomorphism. On a type where the source is larger, choose a surjection whose kernel avoids the span of all chain-coordinate projections of the projected $U$. This span has dimension at most $\ell_i k\le r_i$. On a type where the target is larger, choose an injection whose image contains all chain-coordinate projections of the projected $V$, possible by the same bound. The resulting intertwiner $X$ has $\ker X\cap U=0$ and $V\subseteq\operatorname{im}X$. Choose a complement to its kernel containing $U$, invert $X$ there on its image, and extend that linear map arbitrarily to define $Y$. Then $XY$ fixes $V$ and $YX$ fixes $U$. This gives a solution over the splitting field and proves the lower bound by PC soundness. Each original inverse entry contains at least $n$ distinct monomials.

These are written proofs. Their exact cubic and quadratic exponents concern respectively the unequal-trace worst case and the displayed fixed-gap family. The estimates leave open whether their logarithmic factors are needed.
