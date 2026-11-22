# Polynomial-size IPS for determinant-constrained quiver isomorphism

**Theorem.** Let $k=\mathbb F_q$ be any finite field. Give two explicit representations $A,B$ of the same finite quiver, and prescribe nonzero values for the determinants of the isomorphism at any chosen vertices. Every infeasible instance has a Hilbert-like Ideal Proof System refutation with circuit size polynomial in the explicit input size and $\log q$. The generators are the standard intertwiner and inverse equations below, the prescribed determinants, and the coordinate field equations. There are no auxiliary indeterminates in the refutation other than the IPS placeholders. The ordinary isomorphism case of this proof works over every field and uses no coordinate field equations. The size parameter includes the sum of all vertex dimensions as well as the explicit arrow matrices and determinant data. Equivalently, the bound is polynomial in the size of the explicit equation encoding, with field powers represented by binary exponentiation.

A family of simultaneous operators with named subspaces is included by taking operator loops at the ambient vertex and one inclusion arrow from each marked subspace vertex. The determinant on a marked vertex is then the determinant on that subspace in its given frame. More generally, the theorem allows arbitrary arrows, loops and multiple arrows.

## Exact encoding

At vertex $v$, of dimensions $m_v$ in $A$ and $n_v$ in $B$, write variables $X_v$ of shape $n_v\times m_v$ and $Y_v$ of shape $m_v\times n_v$. For an arrow $a:s\to t$, the written arrow equation is $F_a=X_tA_a-B_aX_s=0$. Both $X_vY_v-I_{n_v}=0$ and $Y_vX_v-I_{m_v}=0$ are written. In equal dimensions the prescribed determinant equation at a marked vertex is $\det X_v-d_v=0$, with $d_v\in k^\times$. If any dimensions differ, the inverse equations alone are inconsistent. The finite-field equations are $z^q-z=0$ for the coordinate variables $z$. Determinant inputs are given by the usual polynomial, represented if needed by a division-free determinant circuit. [Berkowitz](https://doi.org/10.1016/0020-0190(84)90018-8) · [Grochow and Pitassi](https://arxiv.org/abs/1404.3820)

The omitted reverse-arrow equation $Y_t B_a-A_aY_s=0$ has a degree-three derivation in the written generators. Its polynomial is exactly
$$
 (Y_tX_t-I)A_aY_s-Y_tB_a(X_sY_s-I)-Y_tF_aY_s .
$$
The projection and certificate arguments below can equally use a presentation with both arrow directions written.

## The ordinary infeasible case

For $P$ of shape $b\times a$ and $Q$ of shape $a\times b$, with $b>a$, the polynomial $\det(PQ)$ vanishes identically over any field. For example, view $P,Q$ over the fraction field of the polynomial ring and use the rank bound. Replace the rows of $PQ$ one at a time by the rows of $I_b$. The determinant change at each step is linear in the changed row. Expanding by that row gives a signed sum of its entry differences times cofactors of a matrix whose other rows are already fixed. Summing over rows gives a polynomial-size circuit identity expressing $1=\det I_b-\det(PQ)$ as a linear combination of the entries of $PQ-I_b$. The coefficients are sums of polynomially many determinant circuits. This already proves the case of different dimension vectors, by choosing the larger vertex inverse equation.

Now assume identical dimension vectors but no ordinary isomorphism. Form the finite-dimensional algebra $E=\operatorname{End}(A\oplus B)$ of the direct sum representation, with the ordinary morphism rule at each arrow. Write $J=\operatorname{rad} E$, and let $e,f$ be the projection idempotents onto $A,B$. Thus $fEe$ and $eEf$ are the two intertwiner spaces. In a Wedderburn factor $M_r(D)$ of $E/J$, the images of $e,f$ are complementary idempotents. If their ranks over $D$ agreed in every factor, one could choose inverse cross-corner matrices in the quotient and lift them to $x\in fEe$, $y\in eEf$. Then $xy-f\in fJf$ and $yx-e\in eJe$. The corner products are units by nilpotence, so $x$ has both a left and a right inverse in the opposite corner. It is an ordinary isomorphism, a contradiction. Hence at least one factor has different corner ranks.

Take just this factor, represented by its left action on $D^r$ as a vector space over the base field. This gives an algebra map $\rho:E\to \operatorname{Mat}_{r\dim_k D}(k)$. The resulting dimensions of the two corner spaces differ by the nonzero division-ring rank gap multiplied by $\dim_k D$. The matrix size is at most $\dim_k E$, so no extension of the ground field is needed even when the division ring is noncommutative.

Project $X$ and $Y$ separately and linearly onto the two Hom spaces, producing $\widehat X,\widehat Y$. Each entry of $X-\widehat X$ is a scalar combination of the forward arrow equations, and each entry of $Y-\widehat Y$ is a scalar combination of the reverse arrow equations. This is ordinary row-space/kernel duality for the two linear maps given by the arrow equations. Hence the entries of $\widehat X\widehat Y-f$ and $\widehat Y\widehat X-e$ are combinations of the available equations. For instance
$$
 \widehat X\widehat Y-f=(XY-f)+(\widehat X-X)Y+\widehat X(\widehat Y-Y).
$$
Here $XY$ is the vertex-by-vertex product embedded in its block diagonal corner. Apply $\rho$ after extending it linearly from $E$ to the ambient tuple space. Its images on the projected variables multiply exactly, since the projected variables are in the corresponding Hom corners even as polynomial matrices. Restrict to the nonzero blocks of $\rho(e),\rho(f)$. The result is two rectangular inverse equations with different corner sizes. Their original-variable derivations use degree at most three in ordinary Polynomial Calculus: first derive each reverse arrow equation at degree three, then use the resulting linear lines in the degree-two projected products. Substituting the circuit-linear combinations into the determinant identity above gives a Hilbert-like IPS certificate over the ground field. This part supplies polynomial-size circuit refutations for ordinary simultaneous conjugacy nonisomorphism in the encoding of the conjugacy half of Question 7.3. It gives no general polynomial bound on expanded ordinary Polynomial Calculus proof size. [Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3) · [Related simultaneous-similarity rank separators](https://doi.org/10.1016/j.aim.2023.108888)

## The determinant-constrained infeasible case

Fix an ordinary isomorphism $X_0$ and let $E=\operatorname{End}(A)$. Every ordinary isomorphism is $X_0Z$ with $Z\in E^\times$. Over a finite field the semisimple quotient $E/J$ is a product of $M_{r_i}(k_i)$ with $k_i/k$ finite field extensions. On the representation at a marked vertex $v$, the action of $E$ has a composition series. The simple module of factor $i$ is the $r_i$-dimensional column space over $k_i$, considered over $k$. Hence, as a polynomial identity for all coordinates on the vector space $E$,
$$
 \det_k(Z_v)=\prod_i h_i(Z)^{M_{vi}},
 \qquad
 h_i(Z)=N_{k_i/k}\big(\det_{k_i}(\rho_i(Z))\big).
$$
Here $M_{vi}$ is the multiplicity of that simple module, and $\rho_i$ is the quotient map. A composition series gives block-triangular matrices for every $Z$ and proves the identity before any evaluation on field points. The norm formula for a single $k_i$-linear endomorphism follows by extending to an algebraic closure, where the separable tensor product for $k_i/k$ splits into the factors indexed by its embeddings. Alternatively it is the determinant of the underlying $k$-linear representation. This latter description gives a division-free circuit of polynomial size over $k$ for $h_i$, without field-valued gates.

The map $E^\times\to (E/J)^\times$ is surjective. The determinants of the individual factors can attain all values in $k_i^\times$, and each finite-field norm maps onto $k^\times$. Thus the determinant prescriptions are exactly the monomial equations $z^M=a$ on $(k^\times)^u$, where $a_v=d_v/\det (X_0)_v$. This also covers rank-deficient $M$. A Smith form with unimodular multipliers turns the equations into $y_j^{d_j'}=b_j$ for positive Smith entries $d_j'$ and into $1=b_j$ for zero rows. The multipliers have polynomial bit length by the polynomial-time integer Smith algorithm. [Kannan and Bachem](https://doi.org/10.1137/0208040)

If a positive row fails, let $e=\gcd(d_j',q-1)$, and if a zero row fails let $e=q-1$. In either case $e\mid q-1$. Reducing the coefficients of the failed Smith row multiplier modulo $e$ gives exponents $\beta_v\in[0,e-1]$. The constant $c=\prod_v a_v^{\beta_v}$ is outside $(k^\times)^e$, and $e$ divides all $t_i=\sum_v\beta_vM_{vi}$. In the zero-row case this uses $b_j\ne1$ and the fact that the $(q-1)$-th powers in $k^\times$ are exactly 1. Infeasibility in this stage cannot occur when $e=1$.

Project the forward unknowns onto $\operatorname{Hom}(A,B)$ and put $Z=X_0^{-1}\widehat X$. Then
$$
 \prod_v\det(Z_v)^{\beta_v}=\left(\prod_i h_i(Z)^{t_i/e}\right)^e.
$$
Let $R$ be the root given by the product inside the parentheses. It has a polynomial-size circuit, using division-free determinants and binary exponents. All matrices and linear forms in this construction have dimensions polynomial in the explicit input size. Their coefficients are constants of $k$, and the powers have bit length polynomial in the input size and $\log q$. In particular, the root circuit does not enumerate $q$ field elements.

The difference between the outputs of an arithmetic circuit on two input lists is a circuit-linear combination of coordinate differences. At multiplication gates use $uv-u'v'=v(u-u')+u'(v-v')$, retaining the two values at each gate. First apply this to transfer determinant equations from $X$ to $\widehat X$, then apply it to replace $\det(Z_v)$ by $a_v$ in their powered product. This expresses $R^e-c$ as a combination of the written generators with polynomial-size circuit coefficients. Additivity of $q$-Frobenius and $(FG)^q-FG=G^q(F^q-F)+F(G^q-G)$ express $R^q-R$ as a combination of the coordinate field equations, also with polynomial-size circuit coefficients.

Let $\ell=(q-1)/e$ and $S_\ell(x,y)=\sum_{i=0}^{\ell-1}x^{\ell-1-i}y^i$. Since $c\notin(k^\times)^e$, the coefficient $1-c^\ell$ is nonzero. The identity
$$
 R(R^e-c)S_\ell(R^e,c)-(R^q-R)=(1-c^\ell)R
$$
follows by telescoping powers. The polynomial $S_\ell$ has a circuit using $O(\operatorname{poly}(\log q))$ gates by binary recursion on $\ell$. Multiply the identity by $R^{e-1}/(1-c^\ell)$, subtract $R^e-c$, and divide by $c$ to derive 1. Replacing the original equation generators by placeholders gives the stated Hilbert-like IPS proof. All constants have field encodings of $O(\log q)$ bits in a standard explicit field presentation.

This universal finite-field theorem is independent of GRH. The rational prime-transfer result uses GRH only to guarantee a bounded prime probe and imposes its own hypotheses on the stable reduction. The circuit size theorem here has no split-center, rank, Smith-factor or dyadic promise. The proof gives size over explicitly presented finite fields, without a claim that a circuit generator must find the Wedderburn factors in time polynomial in $\log q$. It is a written proof awaiting independent mathematical or kernel review.
