# A quadratic exact-versus-border gap from second-order determinant data

## GP-0577, GP-0579, and GP-0580

For every $s\ge2$, every affine determinantal representation of the generic $s$ by $s$ determinant that has corank one at the zero input has size at least $1+\lceil s^2/2\rceil$. The padded Koszul boundary forms $\mathcal K_{p,k}$ consequently have
$$
\operatorname{dc}(\mathcal K_{p,k})\ \ge\
1+\left\lceil\frac{(c+k)^2}{2}\right\rceil,\qquad
\underline{\operatorname{dc}}(\mathcal K_{p,k})=r+k,
\quad
r=\binom{2p+1}{p},\quad c=\binom{2p}{p-1}.
$$
In particular Sheshadri's explicit degree-$n$ family $\mathcal K_{2,n-10}$ has border complexity $n$ and exact complexity at least $1+\lceil(n-6)^2/2\rceil$ for every $n\ge10$. For the unpadded Koszul form the minimum size just to match the entire coefficient jet through order two, with corank one at the base origin, is $\Theta(r^2)$. The lower bound for this jet problem is $1+\lceil a^2/2\rceil$ for $a=\binom{2p-1}{p-1}$. These are written proofs. [The Koszul families, the regular restriction, and the open questions](https://arxiv.org/html/2611.03554)

### A rank bound over a discrete valuation ring

Let $R$ be a discrete valuation ring with uniformizer $t$, with fraction and residue fields of characteristic zero. Let $M(T)$ be an $m$ by $m$ matrix with entries affine-linear in independent coefficient variables $T=(T_1,\ldots,T_N)$ over $R$. Suppose $D=M(0)$ is of corank one modulo $t$ and $\det D=u t^b$ with $u$ a unit and $b\ge 2$. Write the homogeneous parts of $\det M(T)$ of degrees one and two as $F_1(T)$ and $F_2(T)$. Suppose all coefficients of $F_1$ are divisible by $t^{b-1}$ and all coefficients of $F_2$ by $t^{b-2}$. Then the quadratic form
$$
\overline{t^{-(b-2)}F_2(T)}
$$
over the residue field has rank at most $2(m-1)$. The bar means reduction of each coefficient modulo $t$.

Indeed, an invertible $(m-1)$ by $(m-1)$ minor of $D$ over $R$ lets us use invertible row and column operations over $R$ to make $D=\operatorname{diag}(t^b,I_{m-1})$. The operations are independent of the coefficient variables $T$. They multiply the whole determinant by a unit, which preserves the hypotheses and does not affect the rank of the residue quadratic form. The perturbation remains linear in $T$, and in these coordinates write
$$
M(T)=
\begin{pmatrix}
t^b+\ell(T)&B(T)\\
C(T)&I_{m-1}+W(T)
\end{pmatrix}.
$$
The degree-one part of its determinant is $t^b\operatorname{tr} W+\ell$. Its degree-two part is
$$
t^b e_2(W)+\ell\operatorname{tr} W-B C.
$$
These formulas follow by the Schur complement in the formal $T$-adic expansion of the invertible lower block, keeping degrees at most two. Here $e_2(W)$ is the second elementary coefficient of $\det(I+zW)$.

The first identity forces coefficientwise divisibility of $\ell$ by $t^{b-1}$. In the second identity, the first two terms therefore vanish after dividing by $t^{b-2}$ and reducing modulo $t$. In particular $BC$ is divisible coefficientwise by $t^{b-2}$. Over the fraction field, $BC$ is a sum of at most $m-1$ products of pairs of linear forms, so its quadratic rank is at most $2(m-1)$. Scaling by $t^{-(b-2)}$ preserves this rank over the fraction field. The resulting quadratic has all coefficients in $R$. Every larger minor of its symmetric coefficient matrix vanishes over the fraction field and hence over $R$ and over the residue field. This proves the rank bound. The argument uses rank **before** specialization, so it does not need to bound the number of terms in a product of truncated expansions.

For any $s\ge2$ over a characteristic-zero field, the quadratic form $e_2$ on $\operatorname{Mat}_s$ has rank $s^2$. Its polar form is
$$
(Y,Z)\longmapsto \operatorname{tr}(Y)\operatorname{tr}(Z)-\operatorname{tr}(YZ).
$$
The matrix trace pairing is nondegenerate. An element of the radical must satisfy $Y=\operatorname{tr}(Y)I_s$, so $(s-1)\operatorname{tr}(Y)=0$, and then $Y=0$.

### GP-0579. The regular generic determinant

Given a size-$m$ affine representation of $\det_s(X)$ regular at $X=0$, put $X=tI_s+T$ and use $R=\mathbb C[t]_{(t)}$. The matrix at $T=0$ has determinant $t^s$ and is of corank one modulo $t$ by the stated regularity. The degree-one and degree-two target parts are $t^{s-1}\operatorname{tr}T$ and $t^{s-2}e_2(T)$ respectively. The rank bound gives $s^2\le2(m-1)$, proving the quadratic lower bound.

### GP-0577. The explicit unconditional gap

Sheshadri proves that every determinant representation of the padded form $\mathcal K_{p,k}$ has corank one at every zero and restricts, by a linear coefficient specialization with fixed seed variables, to a representation of a nonzero scalar multiple of $\det_{c+k}$ that has corank one at the zero small matrix. This is the regular-complexity inequality (64), and scaling one constant row removes the scalar. Apply the preceding result to the restricted representation. The cited determinant degeneration and the degree-$r+k$ lower bound for border size give $\underline{\operatorname{dc}}(\mathcal K_{p,k})=r+k$. For $p=2$ one has $r=10,c=4$, so with $k=n-10$ the asserted bound is $1+\lceil(n-6)^2/2\rceil$. [Global corank-one theorem](https://arxiv.org/html/2611.03554#S6.SS3) · [Regular restriction, equation (64)](https://arxiv.org/html/2611.03554#S15) · [Explicit family and its border size](https://arxiv.org/html/2611.03554#S1)

### GP-0580. Sharp order for the complete second-order Koszul jet

Let $v\in\mathbb C^{2p+1}$ and $q(v)=\sum_i v_i^2$. On $\Lambda^p\mathbb C^{2p+1}$ let $X(v)=K(v)C_0(v)$, where $K(v)$ is exterior multiplication by $v$ and $C_0(v)$ is contraction using the standard bilinear form. The source's normalized projection identity for the unpadded Koszul form is
$$
f(v,I_r+T)=q(v)^a\det_r(I_r+X(v)T/q(v)).
$$
The coefficient variable $T$ may range over the full matrix space. If an affine representation is given only on the displayed coefficient complement containing $I_r$, compose it with the fixed linear projection onto that complement. The source identity asserts that the target is invariant when a seed-space element is added to the coefficient matrix. Thus a jet on the complement extends to the full coefficient space. [Projection identity and coefficient complement, equation (65)](https://arxiv.org/html/2611.03554#S17.SS1)

The orders zero, one and two of this identity are $q^a$, $q^{a-1}\operatorname{tr}(XT)$ and $q^{a-2}e_2(XT)$. Suppose a size-$m$ affine pencil agrees with these orders and its base matrix at $v=0,T=0$ has corank one. Work over the discrete valuation ring $\mathbb C[v_1,\ldots,v_{2p+1}]_{(q)}$. Its base matrix has corank one in the residue field: the nonzero $(m-1)$-minor at the origin is a unit in this localization, and the determinant is $q^a$. At a generic isotropic $v$, the residue of $X$ has rank $a$. Indeed, after choosing an isotropic partner $w$ with $(v,w)=1$ and writing $U$ for their common orthogonal complement, the only exterior summand contributing to $K(v)C_0(v)$ is $w\wedge\Lambda^{p-1}U$. It is mapped isomorphically onto $v\wedge\Lambda^{p-1}U$, of dimension $a$. This calculation works over the residue field itself.

For any rank-$a$ square matrix $\bar X$ over a field, $e_2(\bar X T)$ as a quadratic in unrestricted $T$ has rank $a^2$. Choose invertible $U_0,V_0$ with $U_0\bar X V_0=\operatorname{diag}(I_a,0)$. Conjugating $\bar X T$ by $U_0$ and replacing $T$ by $V_0^{-1}TU_0^{-1}$ reduces the claim to the top-left $a$ by $a$ block of the new $T$. That block ranges freely and carries the rank-$a^2$ form just proved. The discrete valuation rank bound gives $m\ge1+\lceil a^2/2\rceil$. The ratio $a/r=(p+1)/(2(2p+1))$ is greater than $1/4$.

For an upper bound, the polynomial
$$
q^{a-2}\left(q^2+q\operatorname{tr}(XT)+
\tfrac12\left((\operatorname{tr}(XT))^2-\operatorname{tr}(XTXT)\right)\right)
$$
is exactly the requested jet and has an algebraic branching program with $O(r^2)$ vertices and affine-linear edge labels. To compute the trace of a product of a constant number of matrices of dimensions at most $r$, use states indexed by the starting index and the current index and accept only matching start and end indices. Substitute the two linear layers $K,C_0$ for each occurrence of $X$. Products and sums of the displayed scalar quantities are obtained by concatenating or taking disjoint unions of a constant number of such programs. The powers of $q$ use $O(a(2p+1))=O(r^2)$ vertices by concatenating two-layer programs for a sum of squares.

In general a scalar branching program on an acyclic graph gives a regular affine determinant, with size at most one plus the number of vertices. To see this, place the program's adjacency matrix $A$ in topological order, so that $I-A$ is unitriangular. The scalar output is the sum of source-to-sink path weights, an entry of $(I-A)^{-1}$. Border $I-A$ by the corresponding constant row and column and a zero corner, choosing one sign so the determinant is that path sum. The invertible unitriangular minor forces corank one at every zero. Applying this construction proves the $O(r^2)$ upper bound in the requested regular class. Together the bounds determine the quadratic asymptotic order of the minimum.
