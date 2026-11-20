# Polynomial-degree tensor nonisomorphism certificates with a bounded mode

**Theorem.** Let $F$ be any field. Let $A,B$ be equal-format three-tensors over $F$, nonisomorphic over an algebraic closure of $F$. Suppose each has flattening ranks bounded, in a common ordering of the three modes, by $m,n,k$. The ordinary cubic action and quadratic two-sided inverse equations of Galesi, Grochow, Pitassi and She have a Nullstellensatz refutation, and hence an ordinary Polynomial Calculus refutation, of degree
$$
(2+m+n+k)^{O(k^2+1)}.
$$
There are no field equations in the refutation. For fixed $k$, the degree is polynomial in tensor rank or border rank, independently of the ambient format. The result covers singular, rectangular, and non-diagonalizable matrix pencils and every fixed-dimensional slice space. It gives a positive answer on the bounded-mode class to the polynomial-degree clause of Question 7.1 and to the geometric degree question in Question 7.4. [Galesi–Grochow–Pitassi–She, §§2.3, 4 and 7](https://arxiv.org/html/2305.19320).

The construction uses the finite restriction and graph lift in the Navier–Stokes certificate. The source retains uneliminated coordinates by the map $r$, takes a graph lift $s(u)=(Lu,u)$, and proves that the projected map covers the retained space. Here the retained coordinates are the nonpivot entries of two witness matrices. On a rank chart their graph lift has $L=-C^{-1}D$. The bordered-minor identity below extends the denominator-cleared lift across the whole determinantal set, including at singular pivots. This lift eliminates the large witness matrices from the effective Nullstellensatz step, leaving just $k^2$ slice coordinates. [Alpöge–Buckmaster, tree_final and its restriction and lift](https://github.com/tristanbuckmaster/navier-stokes/blob/ad53419de079eb8f95f60313473374624a348546/lean/Breakdown/FracCell/TreeFinal.lean#L87-L149).

## 1. Compress the original equations

For a polynomial $f$, a certificate of degree $D$ for $f=0$ is an identity $f=\sum_i h_i e_i$ in which the $e_i$ are original axiom polynomials and every summand has total degree at most $D$. Multiplying by a polynomial adds at most its degree to the bound. Replacing an intermediate equation by a certified identity adds at most the certificate's degree overhead above the degree of the intermediate equation.

If $R-S$ has certified entries, the difference of their corresponding $t$-minors has a certificate. In each determinant monomial, telescope the product by replacing one factor at a time. Each difference entry is multiplied by at most $t-1$ other entries. This works over any field. We also use Cauchy–Binet for rectangular products as a polynomial identity.

The intrinsic supports are the column spaces of the three flattenings. Independently adapt the source and target bases to those supports. This is a constant invertible linear change of the witness variables, and the transformed equations are constant linear combinations of the originals.

Suppose a flattening of $A$ has rank $t-1$ and the corresponding one of $B$ has larger rank. The action says $\mathrm{Flat}_i(B)=X_i\mathrm{Flat}_i(A)(X_j\otimes X_\ell)^{\mathsf T}$. By Cauchy–Binet every $t$-minor of the right-hand side is identically zero. Comparing with a nonzero constant $t$-minor of $\mathrm{Flat}_i(B)$ gives a refutation in degree at most $3t$. The reverse action is certified in degree at most six by applying the three inverses to the action and telescoping the three inverse identities. Thus a larger rank in $A$ is handled with degree at most $3t+3$. This includes comparison to the zero tensor.

Assume the supports have equal dimensions. Cancel the other two actions on the right of the flattening identity using their transposed inverses. The bottom rows of $\mathrm{Flat}_i(B)$ vanish, so this gives
$$
(X_i)_{\mathrm{bottom,top}}\cdot \mathrm{Flat}_i(A)_{\mathrm{top},*}=0 .
$$
The constant matrix on the right has full row rank and a constant right inverse. Applying it proves the vanishing of the bottom-left block of $X_i$. Applying the reverse action gives the same conclusion for $X_i'$. Top-left blocks of both inverse identities, together with the vanishing blocks, certify both inverse identities on the supports. The compressed tensor action is directly the top-left part of the original action. Thus all compressed axioms have constant-degree certificates in the original equations. The compressed tensors are nonisomorphic, since an isomorphism on supports would extend by arbitrary isomorphisms of the complements.

We may now use $m,n,k$ for the actual nonzero compressed dimensions and assume $A$ is concise in the third mode. In particular $A(x)=\sum_i x_i A_i$ is injective as a linear map of $x$.

## 2. Certify a single rank for the intertwiner system

Use the equivalent convention $P A_i=B(Ze_i)Q$, with two-sided inverses $P',Q',Z'$. Indeed the raw tensor action is $B(x)=P A(W^{\mathsf T}x)R^{\mathsf T}$. Choose $Q=(R')^{\mathsf T}$ and $Z=(W')^{\mathsf T}$, substitute $Zx$, and right-multiply by $Q$. The equations follow in constant degree using $W^{\mathsf T}Z=I$ and $R^{\mathsf T}Q=I$. The inverses are $P',R^{\mathsf T},W^{\mathsf T}$.

Define the matrix of linear constraints on a candidate pair $(U,V)$ by
$$
E(Z)(U,V)=(UA_i-B(Ze_i)V)_{i=1}^k .
$$
Here $U$ and $V$ have sizes $m$ and $n$. Let $E_0(U,V)=(UA_i-A_iV)_i$ be the constant self-intertwiner matrix and set $r=\mathrm{rank}\,E_0$. Let $L_{P,Q}$ left-multiply the two inputs by $P,Q$, respectively, and let $C_P$ left-multiply each output matrix by $P$. Then
$$
E(Z)=C_PE_0L_{P',Q'},\qquad E_0=C_{P'}E(Z)L_{P,Q}
\tag{1}
$$
hold entrywise modulo the original equations with constant-degree certificates. For the first, at each fixed basis input $(U,V)$, subtract $P(P'UA_i-A_iQ'V)$ from $UA_i-B(Ze_i)V$ and use $PP'=I$ and $B(Ze_i)=PA_iQ'$. The latter equation follows by right multiplication of $PA_i=B(Ze_i)Q$ by $Q'$ and using $QQ'=I$. For the second, compare $P'((PU)A_i-B(Ze_i)QV)$ with $UA_i-A_iV$, using $P'P=I$ and the pencil equations.

Every $(r+1)$-minor $g$ of $E(Z)$ therefore has a certificate of degree $O(r+1)$. A corresponding minor of $C_PE_0L_{P',Q'}$ is identically zero by Cauchy–Binet, and determinant expansion certifies the difference. If there are no minors of order $r+1$, the determinantal condition below is vacuous.

Choose a nonzero constant $r$-minor of $E_0$. The second equality in (1) and Cauchy–Binet express this constant, modulo a certificate of degree $O(r+1)$, as a linear combination of $r$-minors of $E(Z)$, with coefficients of degree at most $2r$ in the transporter variables. Let $d_1,\ldots,d_M$ be a basis selected from those minors. Express all minors in that basis by constant linear combinations and divide by the nonzero constant. The resulting certificate is for
$$
1-\sum_{j=1}^M a_jd_j=0,\qquad \deg a_j\le 2r.
\tag{2}
$$
There are only $q=k^2$ entries of $Z$, so $M\le(r+1)^q$. All matrices of the nonzero compressed tensor have positive dimensions, and $E_0=0$ would force $A_i=0$ for all $i$ by applying it to $(I,0)$.

## 3. Lift on each pivot and eliminate the large witness matrices

Fix $d_j$ and let $C$ be its selected square submatrix, $D$ the remaining columns of its selected rows, and $d=\det C=d_j$. Define, in pivot and free coordinates respectively,
$$
K(v)=\bigl(-\operatorname{adj}(C)Dv,\ d v\bigr).
$$
The selected rows of $E(Z)K(v)$ vanish identically. For an unselected row with pivot part $c$ and free part $e$, the coefficient of $v_\ell$ is
$$
d\,e_\ell-c\,\operatorname{adj}(C)D_{*,\ell}
=\det\begin{pmatrix}C&D_{*,\ell}\\ c&e_\ell\end{pmatrix}.
\tag{3}
$$
Cofactor expansion gives (3), including at $d=0$. Hence $E(Z)K(v)=0$ whenever every $(r+1)$-minor vanishes. On $d\ne0$, $K(v)/d$ is the graph lift of the free coordinates.

Reshape $K(v)$ into matrices $K_U(v),K_V(v)$. Set $h=m+n$ and $p(Z,v)=\det K_U(v)\det K_V(v)$. At every $Z$ over the algebraic closure at which the $(r+1)$-minors vanish, $p(Z,v)=0$ for every $v$. Otherwise $K_U(v),K_V(v)$ are invertible and solve the intertwiner equations. If $Zx=0$, these equations give $K_U(v)A(x)=0$ and hence $A(x)=0$. Conciseness gives $x=0$. Thus $Z$ would be invertible, contradicting geometric nonisomorphism. Since the algebraic closure is infinite, every coefficient of $p(Z,v)$ in $v$ vanishes on the determinantal variety.

These coefficients have degree at most $hr$ in $Z$. Put $\Delta=\max(2,r+1,hr)$ and express $p(Z,v)=\sum_i c_i(Z)\lambda_i(v)$ where $c_1,\ldots,c_L$ is a basis selected from the coefficient polynomials and $\lambda_i$ is homogeneous of degree $h$. Then $L\le(\Delta+1)^q$. The effective radical Nullstellensatz in $q$ variables certifies $c_i^{D_i}$ in the ideal of the $(r+1)$-minors, with $D_i$ and the product-degree bound at most $\Delta^{O(q+1)}$. For example, apply Sombra's Corollary 2.11 to the normal simplex of side $\Delta$, whose normalized volume is $\Delta^q$. Certificates over the algebraic closure descend to $F$ by solvability of the same finite linear system for coefficients. If there are no higher minors, every coefficient is identically zero and the radical step is omitted. Take a common integer bound $D_*\ge1$ on all $D_i$ across all pivots. Multiplying by $c_i^{D_*-D_i}$ and substituting the certified higher minors gives certificates for all $c_i^{D_*}=0$ of degree $\Delta^{O(q+1)}$. [Sombra, *A Sparse Effective Nullstellensatz*, Corollary 2.11](https://doi.org/10.1006/aama.1998.0633).

Set $E_*=D_*(\Delta+1)^q$, the same for all pivots. Every term in the expansion of $p^{E_*}$ as a product of the summands $c_i\lambda_i$ is divisible by some $c_i^{D_*}$, since fewer than $D_*$ occurrences of each of $L$ summands would give fewer than $LD_*\le E_*$ factors. This certifies $p^{E_*}=0$ with degree $\Delta^{O(q+1)}$. The empty-basis case $p=0$ gives the same conclusion. Specialize $v$ to the actual free coordinates of the transporter $(P,Q)$, a degree-one substitution.

## 4. Assemble the pivot certificates

On the actual transporter, the selected rows say $Cx_{\mathrm{pivot}}+Dv=0$. Multiplying by $\operatorname{adj}(C)$ gives $d(P,Q)=K(v)$ entrywise modulo the pencil equations. Taking determinants gives $p(Z,v)=d^h\det P\det Q$ via the product-difference expansion, with certificate degree $O(h(r+1))$. Applying the determinant difference expansion to the inverse equations gives $\det P\det P'=\det Q\det Q'=1$ with degree $O(h)$. Thus $d^h=p(Z,v)\det P'\det Q'$ has a certificate of degree $O(h(r+1))$. Raise to $E_*$ using $a^t-b^t=(a-b)\sum_{i=0}^{t-1}a^i b^{t-1-i}$, and substitute the certificate for $p^{E_*}=0$. This certifies every $d_j^H=0$ in degree $\Delta^{O(q+1)}$ for the common $H=hE_*$.

Finally put $S=\sum_{j=1}^M a_jd_j$ and $N=M(H-1)+1$. Every term of $S^N$ contains some $d_j^H$, so the pivot certificates give $S^N=0$. Equation (2) and the difference-of-powers identity certify $1-S^N=0$. Add the certificates. The assembly adds at most $O(rN)$ to the degree, with $r\le m^2+n^2$, $M\le(r+1)^q$, and $N\le MH$. This proves the claimed bound. Expand each coefficient into monomials, multiply the original axioms by those monomials, and take linear combinations to get ordinary Polynomial Calculus of the same degree.

For the border-rank conclusion, the Zariski-closed conditions that each flattening rank is at most $b$ contain every tensor of rank at most $b$, so they contain its closure. Thus one can take $m,n\le b$ for tensors of border rank at most $b$. For ordinary tensor rank the same bounds follow directly from a sum of rank-one tensors.

## Verification scope

This is an informal proof of a uniform degree upper bound. The argument uses a fixed-small-mode hypothesis for the polynomial-in-rank bound and supplies no new sparse-size guarantee. The Navier–Stokes input is its finite restriction and graph-section construction, adapted algebraically over arbitrary fields.
