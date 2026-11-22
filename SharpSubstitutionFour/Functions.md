# Recovering the hidden quadratic space from nonlinear matrix substitutions

**Theorem.** Let $V$ be a finite-dimensional vector space over any field $k$. Let $H,H'\subseteq\operatorname{Sym}^2V$ contain no nonzero sum of two products of linear forms. Use the same padded dimension for their quotients, and form the square-zero pencils
$$
L_H(r,u)=rI+N_{H,u},\qquad
N_{H,u}(v,w)=(0,[uv]_H)
$$
on $J_H=V\oplus W_H$, where $W_H$ contains the quotient $\operatorname{Sym}^2V/H$ as a summand and the rest is inert. Define
$$
\sigma(H,H')=\min\{\ell(f):f\in H\mathbin{\triangle}H'\},\qquad
\ell(f)=\min\{d:f=\textstyle\sum_{i=1}^d u_iv_i\}.
$$
Set $\sigma=\infty$ when $H=H'$. With the parameter coordinates fixed, the first matrix-substitution size that distinguishes the two pencils by rational canonical form is exactly $\sigma$. This holds also for the variant $N_{H,u}\oplus N_{H,u}^{\mathsf T}$, which yields symmetric square slices using the fixed hyperbolic pairing.

At **every** matrix size the two pencils give identical syntactic domains, determinants and characteristic polynomials for arbitrary noncommutative rational expressions in any finite collection of their substituted matrices. The expressions may have fixed matrix coefficients on the substitution leg. At sizes less than $\sigma$ every defined expression has the same rational canonical form. At size $\sigma<\infty$ a single centered linear matrix substitution separates the pencils, and the same substitution distinguishes the ranks of a minimal resolvent realization minus the identity. The comparison and recovery hold over the operating field in every characteristic.

These statements have a final-digit version over a finite commutative local ring $R$ with residue field $k$ and supplied $0\ne s\in\operatorname{Ann}(\mathfrak m)$. The product in $N$ is then the residue product included coefficientwise into $sR$. At every level the syntactic domains and characteristic polynomials still coincide. Below $\sigma$ the images of corresponding expression values have equal cardinalities, even for nonprincipal $R$. Over chain rings the Smith forms of every defined expression value coincide below $\sigma$. At $\sigma$ the separating substitution gives different image orders, and therefore distinct Smith forms on chain rings.

The preceding tensor reduction supplies such $H_M$ with $\sigma\ge h+1$, keeps the dense output polynomial in $h$ and the input size, and reflects arbitrary tensor transporters. Thus these observations can agree for polynomially many matrix sizes while the pencil isomorphism problem retains the complexity of ordinary tensor isomorphism. [Square-zero pencil construction](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md).

## 1. Closure of the square-zero matrix calculus

Write $\pi_H\colon\operatorname{Sym}^2V\to W_H$ for the quotient inclusion. In the ring version set $j:k\to sR$, $\bar a\mapsto sa$, an $R$-module isomorphism since the annihilator of $s$ is exactly $\mathfrak m$. Use $j=\mathrm{id}$ in the field case. At matrix size $q$, after reordering the basis, a substituted matrix has the form
$$
\Phi_H(A,U)=
\begin{pmatrix}
 A\otimes I_V &0\\
 j(B_H(U)) & A\otimes I_W
\end{pmatrix},
\qquad
\big(B_H(U)v\big)_i=\sum_{j'=1}^q\pi_H(u_{ij'}v_{j'}).
\tag{1}
$$
Here $A\in M_q(R)$ and $U=(u_{ij'})\in M_q(V)$, with the latter space interpreted over $k$. The lower block is inserted using fixed basis lifts. Each input can have its own $A,U$. A fixed external matrix coefficient $C$ means $C\otimes I_{J_H}$.

The parameters add componentwise and multiply by
$$
(A,U)(C,T)=(AC,\ \bar A T+U\bar C).
\tag{2}
$$
This follows from scalar-block multiplication and the vanishing of every product of two centered operators. If $A$ is invertible, the inverse has parameters
$$
(A^{-1},-\bar A^{-1}U\bar A^{-1}).
\tag{3}
$$
Conversely invertibility of $\Phi_H(A,U)$ implies that of $A$ by its determinant $\det(A)^{\dim J_H}$. All these identities also hold with the transpose companion, because its centered products vanish and the same formulas act coefficientwise on its $q$-indexed blocks. The optional inert norm-one line for the dyadic ring variant contributes just $A$.

Induction on an expression made of sums, products and inverses now determines its domain and, when defined, the pair $(A_r,U_r)$ from the common scalar-block data alone. Its determinant and characteristic polynomial are $\det(A_r)^{\dim J_H}$ and $\det(TI_q-A_r)^{\dim J_H}$, with the corresponding total dimension for the companion. Each inverse gate is tested independently by (3), so this is equality of the domain of **each written expression**, including expressions with removable singularities under other representatives.

For free rational functions over a field in the usual sense, use the ordinary domain given by the union of evaluable representatives. The same representatives are defined on the two tuples, so those ordinary domains agree as well. Values can be compared using any common evaluable representative. This assertion concerns that union, distinct from the extended domain defined by generic entrywise rational expressions. Section 4 treats extended domains directly for the particular resolvent. [Kaliuzhnyi-Verbovetskyi–Vinnikov, *Noncommutative rational functions, their difference-differential calculus and realizations*](https://arxiv.org/abs/1003.0695) · [Volčič, *On domains of noncommutative rational functions*](https://arxiv.org/abs/1608.02594).

## 2. Every output below the first differing product length

If $\dim U_0<\sigma$, then $H\cap U_0V=H'\cap U_0V$. Indeed each element of $U_0V$ is a sum of at most $\dim U_0$ products, obtained by using a basis of $U_0$ as first factors. The images of $U_0V$ in the two $W$-spaces are thus identified by the map taking each projected product to its counterpart. This map extends to an isomorphism of the equally dimensional $W$-spaces.

For $q<\sigma$ over a field or chain ring, diagonalize the common scalar block $A_r$ of (1) by independent external row and column operations. For each resulting block row, use the span $U_0$ of its up to $q$ directions. The corresponding extension on $W$ matches that entire block row of $B_H$ to its counterpart. On a chain ring lift the extension from the residue field, possible by invertibility of the residue matrix. Apply the direct sum of these $W$-maps, one per block index, and identity on the $V$-parts. It conjugates the transformed matrices since the scalar blocks are diagonal. Undoing the initial row and column operations gives left-right equivalence and hence the same Smith form over a chain ring. On the transpose companion use the spans of columns and the maps on $W^*$ instead. This also gives left-right equivalence there.

Over a field apply the same result to every polynomial in the output expression, which is again an expression. The nullities of all powers of every monic irreducible polynomial in a matrix determine its elementary divisors. Hence each pair of defined outputs below $\sigma$ has the same rational canonical form over the field itself.

For any finite local $R$, one can compare image sizes without diagonalization. Put $C=\operatorname{im}A_r$ and $K=\ker A_r$ in $R^q$. Projection to the $V$-component in (1) has image $C^D$, where $D=\dim V$. The vertical kernel of this projection on the image of (1) is
$$
C^{\dim W} + j(B_H(U_r))(K^D).
$$
In the quotient by $C^{\dim W}$ the second summand is the image of a $k$-linear map from $\bar K\otimes V$ to $(k^q/C_s)\otimes W$, with $\bar K$ the image of $K$ under reduction and $C_s=j^{-1}(C\cap (sR)^q)$. In bases for the residue source and target array indices the map still has product blocks of the form $B_H$, since restriction to $\bar K$ and projection modulo $C_s$ make common scalar linear combinations of the blocks. Each row has at most $\dim\bar K\le q$ directions. The same extension on each row matches these images and their dimensions. Multiplying the sizes of $C^D$, $C^{\dim W}$, and this vertical quotient proves equal image orders. The transpose companion follows by using columns for the residue-compressed transpose blocks. This gives the finite-local result for each rational expression.

## 3. One rank query recovers membership of a quadratic

Let $f$ be a nonzero quadratic of product length $q\ge2$. Choose $f=\sum_{i=1}^q u_iv_i$ with $v_1\ne0$. The following test also works for any longer decomposition of a nonproduct quadratic. Form the $q\times q$ direction array $U_f$ whose first row is $u_1,\ldots,u_q$, and whose row $j\ge2$ has $v_j$ in column one, $-v_1$ in column $j$, and zero elsewhere. If $w=(w_1,\ldots,w_q)$ lies in the kernel of the last $q-1$ rows of $B_H(U_f)$, then
$$
v_jw_1-v_1w_j\in H \qquad (j\ge2).
$$
Each polynomial on the left is a sum of two products, so it vanishes in the polynomial ring. Some $v_j$ is independent of $v_1$, since otherwise $f$ would be a single product. In that equation divisibility forces $w_1=\lambda v_1$, and every other equation then forces $w_j=\lambda v_j$. The kernel of these rows is exactly the indicated line. The first row retains the line precisely if $f\in H$, since its restriction is $\lambda[f]_H$. This gives the exact rank
$$
\operatorname{rank}B_H(U_f)=qD-\mathbf 1_{\,f\in H}.
\tag{4}
$$
Signs require no division by two, so characteristic two is included.

For the normalized transpose companion the additional block is the transpose of $B_H(U_f^{\mathsf T})$. In the array $U_f^{\mathsf T}$, the constraint rows are $u_jw_1-v_1w_j$ for $j\ge2$. At least one of these $u_j$ is nonproportional to $v_1$, since otherwise every term of $f$ would contain $v_1$ and $f$ would be a product. The same argument forces the line $\lambda(v_1,u_2,\ldots,u_q)$, and the remaining row again tests $\lambda[f]_H=0$. The two rank jumps therefore add. Over a final-digit ring the rank-$r$ residue block has image size $|k|^r$ under the coefficient embedding $j$, so the same test applies to image sizes.

If $f$ is chosen in $H\triangle H'$ of minimum product length, then $q=\sigma\ge3$ by hypothesis. Put $A=0$ and use $U_f$. Formula (4) distinguishes the two pencils, and Sections 1–2 show that no nonlinear rational expression can distinguish their spectral or Smith data at a smaller size. This proves the pair-specific first size. Conversely identical spectral data at every size recovers equality $H=H'$ in the fixed coordinates. More explicitly, (4) tests membership of any nonproduct quadric from a decomposition. Nonzero individual products are automatically excluded. If bases of the two differing spaces are given, Gaussian elimination finds a differing quadric, and grouping its monomials by first basis variable gives a decomposition of length at most $D$. Thus a deterministic separating substitution of size at most $D$ requires only polynomial work on the explicit inputs. The optimal size statement uses the minimum product length and does not require an algorithm to find that minimum.

## 4. Minimal resolvents with the same domains

Over a field consider the $n\times n$ matrix of free rational functions
$$
F_H(X)=\left(I-X_0I_n-\sum_{\nu=1}^D X_\nu N_{H,e_\nu}\right)^{-1},
\qquad n=\dim J_H.
$$
Use the same normalized formula for the transpose companion. At level $q$ this is the inverse of $I-\Phi_H(X_0,U)$. Its precise domain is $\det(I_q-X_0)\ne0$. For this particular function the same holds for the entrywise extended domain. To see the reverse inclusion, if all rational entries of $F_H$ are regular at a tuple, evaluate the generic identity $(I-\Phi_H(X_0,U))F_H=I$ there. The evaluated matrix $I-\Phi_H(X_0,U)$ must be invertible, forcing the condition on $X_0$. The set is stable under direct sums, so it is also the stable extended domain. This argument can be made after any field extension and does not assume that every rational expression in Section 1 has this extended-domain property.

In the standard realization at zero
$$
D_0+C\left(I-\sum_\nu A_\nu X_\nu\right)^{-1}\sum_\nu B_\nu X_\nu,
$$
the coefficient of the word $X_0$ is $CB_0$. For $F_H$ it is $I_n$, so every such realization has at least $n$ states. The displayed $n$-state resolvent realizes this bound by taking $C=D_0=I_n$, $A_0=B_0=I_n$, and $A_\nu=B_\nu=N_{H,e_\nu}$ for $\nu>0$. The argument over a local coefficient ring gives the same lower bound for free state modules by reducing that first coefficient to the residue field.

The previous tensor reduction supplies a parameter change on $V$ fixing the scalar coordinate and a fixed output conjugacy for every input transporter. This conjugates the corresponding resolvent after the same variable change. Conversely equality of these functions under such a variable change and output conjugacy yields equivalence of the original pencils, by inverting or comparing their linear coefficients at zero. Thus the isomorphism promise becomes a promise on minimal state realizations. Below $\sigma$ their values have the common spectral or Smith data of Section 2. At the separating substitution $X_0=0$ the resolvent is $I+\Phi_H(0,U_f)$, since the centered term squares to zero. Subtracting $I$ exposes the membership jump of (4) at exactly the first size.

The realization convention and free-domain distinctions follow standard noncommutative systems theory. The product length is quadratic strength, the degree-two case of the strength decompositions studied by Bik and Oneto. The specific result here is the rank-membership test, its exact first-level consequence and preservation under nonlinear rational calculus. The preceding sharp construction already separated particular matrix slices at a prescribed size; the present test works for arbitrary kernels satisfying the two-product exclusion and requires no distinguished anchor among the directions of a decomposition. This is an informal proof. Publication priority for this package remains unverified. [Porat–Vinnikov, *Realizations of non-commutative rational functions around a matrix centre I*](https://arxiv.org/abs/1905.11304) · [Bik–Oneto, *On the strength of general polynomials*](https://arxiv.org/abs/2005.08617) · [Grochow–Qiao IV](https://arxiv.org/html/2306.16317).
