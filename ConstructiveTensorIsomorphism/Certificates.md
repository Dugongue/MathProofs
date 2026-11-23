# Sparse Polynomial Calculus for the connected spectral tensor class

Let \(F\) be any field, \(d=2h\ge4\), \(n\ge2\), and \(T,U\) ordered \(d\)-tensors in \((F^n)^{\otimes d}\). The action equations say \((\bigotimes_i G_i)T=U\). For each mode there is an independent inverse matrix \(G_i'\) and both inverse equations \(G_iG_i'=G_i'G_i=I\). Ordinary Polynomial Calculus uses scalar linear combinations and multiplication by a single variable. Size below is the total number of expanded monomials over proof lines. The written system includes no coordinate field equations and no extension variables.

Use the balanced-cut spectral covariants of the earlier even-order comparison. The connected spectral class consists of tensors with invertible balanced cut, separable characteristic polynomial for each mode covariant, and connected overlap graph in each split spectral frame. In mode \(i\), the graph joins two spectral labels when they have a common context of nonzero entries in all other modes. The graph condition has a rational linear-algebra test. [Earlier spectral covariants, including even order and every characteristic](https://github.com/Dugongue/MathProofs/blob/main/GenericOrdinaryFourTI/PROOF.md)

**Theorem 1.** If \(T\) lies in the connected spectral class, exactly one of the following holds.

- There is a transporter over \(F\).
- The literal action and inverse equations have an ordinary Polynomial Calculus refutation of degree at most \(8d\) and expanded size \(n^{O(d)}\). They also have a Nullstellensatz identity of total-product degree \(O(d)\) with \(n^{O(d)}\) expanded monomials in its coefficients.

The constants in these bounds are absolute. The degree order in \(d\) is sharp in the action encoding, since the inverse axioms alone are consistent and every action axiom has degree \(d\) when \(T\ne0\). On explicit finite fields the algorithm recognizes the source class and constructs the transporter or refutation by deterministic polynomial-bit-time arithmetic in the full dense input size and \(\log|F|\), with no factoring premise. For \(F=\mathbb F_q\) and \(n\ge37\), the source class has uniform density at least \(1-32d^2n^{h+3}/q\). For each accepted source the conclusion holds against every target.

## 1. Literal equations imply linear mode intertwining

Let \(M,N\) be the balanced flattenings of \(T,U\). Write
\[
 X=\bigotimes_{i\le h}G_i,\qquad
 Y=\bigotimes_{i>h}G_i,\qquad E=N-XMY^{\mathsf T}.
\]
Use \(X',Y'\) for the corresponding Kronecker products of the supplied inverse matrices. All entries of \(E\) are literal action axioms up to sign. The Kronecker inverse equations are derived by telescoping over the individual inverse equations, since matrix multiplication of Kronecker products is componentwise.

Set \(B=Y'^{\mathsf T}M^{-1}X'\), using the constant matrix \(M^{-1}\). The polynomial identity
\[
 NB-I=EB+XM\big((Y'Y)^{\mathsf T}-I\big)M^{-1}X'+(XX'-I)
\tag{4}
\]
derives the entries of \(NB-I\) with degree at most \(2d\). If \(N\) is singular, multiply by a nonzero constant left nullvector of \(N\) and take one nonzero coordinate to obtain a contradiction. Otherwise multiply by the constant \(N^{-1}\). Upon transposing, the result is the inverse-tensor equivariance
\[
 N^{-{\mathsf T}}
   =X'^{\mathsf T}M^{-{\mathsf T}}Y'
\tag{5}
\]
as a vector of derived equations. Here \(M^{-{\mathsf T}}\) is written as a tensor with one contravariant slot per mode.

Each spectral covariant \(A_i\) uses four copies of the input tensor and four copies of its contravariant inverse tensor. In mode \(j\) the contraction matches the four positive and negative slots, except for one removed edge in mode \(i\). Write the opened contraction on \(U\), and compare it to the same expression with its four positive arrays replaced by \((\bigotimes_jG_j)T\) and its four negative arrays replaced using (5). Subtract by replacing one factor at a time. Each scalar coefficient in this comparison is a product of at most seven transformed array entries times constants and summation. Multiplying a stored copy of a derived degree-\(d\) equation by one of these expanded coefficients stays within degree \(8d\). The use of (5) as a stored line keeps its initial degree-\(2d\) construction separate.

In the fully transformed contraction, each closed edge pairs a \(G_j\) and the inverse-dual matrix \(G_j'^{\mathsf T}\). Sum over their shared output index to give the appropriate entry of \(G_j'G_j\). Replace all these entries by the corresponding identity entries, telescoping in the same way. Each open edge contributes one forward or inverse matrix entry, and each mode contributes at most eight matrix entries before cancellation. The result is the derived equation \(A_i(U)-G_i A_i(T)G_i'=0\). Multiplying by \(G_i\) on the right and applying \(G_i'G_i=I\) gives the linear entries of
\[
 A_i(U)G_i-G_i A_i(T)=0 .
\tag{6}
\]
Multiplying (6) by \(G_i'\) on both sides and correcting inverse products gives the reverse intertwining lines. The last two preparations have degree at most three once the preceding lines have been stored.

If the characteristic polynomials \(f_i(T),f_i(U)\) differ, set \(p=f_i(T)/\gcd(f_i(T),f_i(U))\). This is nonconstant and coprime to \(f_i(U)\), since \(f_i(T)\) is squarefree and the polynomials have the same degree. The matrix \(p(A_i(T))\) has a nonzero kernel and \(p(A_i(U))\) is invertible. Both assertions follow by scalar polynomial calculus on the constant matrices, or by checking eigenvalues after base change. The linear equation
\[
 p(A_i(U))G_i-G_i p(A_i(T))=0
\]
is a scalar linear combination of (6), by telescoping the powers of the constant matrices. Apply it to a nonzero constant kernel vector \(v\) of \(p(A_i(T))\), then multiply by the constant \(p(A_i(U))^{-1}\). This derives \(G_i v=0\). The inverse axiom gives \(v=0\) in degree two. Thus the remaining case has identical squarefree characteristic polynomials in every mode.

## 2. Support and overlap yield complete linear obstructions

Let \(K_i=F[z_i]/(f_i(T))\), and let \(K=\bigotimes_i K_i\). Each matrix \(A_i(T)\) or \(A_i(U)\) has minimal polynomial \(f_i(T)\), since its characteristic polynomial is squarefree. Identify its mode space with \(K_i\) using a constant cyclic basis. Write \(t,u\in K\) for the two tensors in these bases. Over finite fields a constructive module-isomorphism algorithm identifies each matrix with its companion matrix deterministically. It only needs the equality of their invariant factors already established above. [Brooksbank–Luks, Testing Isomorphism of Modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

In the two chosen mode bases, the linear equation (6) says that \(G_i\) is multiplication by an element \(g_i\in K_i\). Explicitly, take \(g_i\) to be the image of \(1\) under the changed-basis map, whose coordinates are linear forms in the original variables. For every standard power \(z_i^j\), repeatedly commute \(z_i\) past that map using (6). This gives all linear equations saying that the respective column is \(z_i^j g_i\). The same argument gives \(G_i'\) as multiplication by \(h_i\), also a vector of linear forms. Substitute these linear representations into the inverse and action equations by a factor-by-factor difference, and take coordinates in the output algebras. The derived equations are
\[
 g_i h_i-1=0 \quad\text{in }K_i,\qquad
 u-\left(\bigotimes_i g_i\right)t=0\quad\text{in }K.
\tag{7}
\]
The proof degree for this substitution is at most \(d\), since at most one factor from each mode occurs in an action coordinate. To obtain
\[
 t-\left(\bigotimes_i h_i\right)u=0 ,
\tag{8}
\]
multiply the second equation of (7) by \(\bigotimes_i h_i\) and use the inverse equations of (7) in each slot. This uses degree at most \(2d\).

Support is tested without decomposing a field or factoring a polynomial. Solve the constant linear equation \(t^2 a=t\) in \(K\). It is soluble because \(K\) becomes a product of copies of the algebraic closure after base change. The linear equations descend, and \(e_t=ta\) is the idempotent equal to one on the split support of \(t\) and zero elsewhere. Construct \(e_u\) in the same way. Multiplying (7) by \(1-e_t\) gives the constant \((1-e_t)u=0\). Multiplying (8) by \(1-e_u\) gives \((1-e_u)t=0\). Any different support yields a nonzero coordinate of one of these constant equations. Hence assume the two split supports agree.

For mode \(i\) form the algebra
\[
 L_i=K_i\otimes K_i\otimes\bigotimes_{j\ne i}K_j .
\]
The superscripts \(^{(1)},{}^{(2)}\) denote its two maps from \(K\), which share all slots except \(i\). The same superscripts on an element of \(K_i\) select its first or second copy. The source recognition condition is that the following linear map on \(K_i\) have one-dimensional kernel for all \(i\):
\[
 x\longmapsto t^{(1)}t^{(2)}(x^{(1)}-x^{(2)}).
\tag{9}
\]
Indeed, over the split field its kernel imposes equality exactly on the edges of the overlap graph. This proves the test by rational Gaussian elimination.

Apply the two maps to the action equation of (7) and subtract their suitable linear multiples:
\[
 \begin{split}
 &t^{(2)}g_i^{(2)}
       \left(u^{(1)}-t^{(1)}g_i^{(1)}\prod_{j\ne i}g_j\right)
 -t^{(1)}g_i^{(1)}
       \left(u^{(2)}-t^{(2)}g_i^{(2)}\prod_{j\ne i}g_j\right)\\
 &\qquad =u^{(1)}t^{(2)}g_i^{(2)}-u^{(2)}t^{(1)}g_i^{(1)} .
 \end{split}
\tag{10}
\]
The products over \(j\ne i\) use the shared slots. The multilinear terms cancel identically in the commutative algebra \(L_i\). Equation (10) therefore derives every coordinate of a linear equation on \(g_i\), using degree at most \(d+1\).

In split coordinates on an edge \(a,b\) in mode \(i\), (10) identifies \(g_{i,a}\) and \(g_{i,b}\) up to a nonzero fixed factor, since both tensor entries at the witnessing context are nonzero in both tensors. This argument only needs matching supports. Connectivity forces the linear kernel to have dimension at most one even on a negative target. If that dimension is zero, scalar combinations of (10) give all coordinates of \(g_i=0\). Combining with the inverse equation in (7) refutes in degree two after storing the linear lines. If it is one, a nonzero rational generator \(x_i\in K_i\) has every split coordinate nonzero, again by edge propagation. Therefore \(x_i\) is a unit. Row reduction gives linear equations
\[
 g_i=\lambda_i x_i
\tag{11}
\]
where \(\lambda_i\) is one linear form in original entries of \(G_i\), obtained by normalizing at a nonzero coordinate in the rational basis.

Set \(v=(\bigotimes_i x_i)t\), a fixed nonzero vector. Substitute (11) into the action equation of (7), telescoping over the \(d\) slots. This derives
\[
 u-\left(\prod_i\lambda_i\right)v=0 .
\tag{12}
\]
If \(u\) is outside the \(F\)-line of \(v\), a constant linear functional killing \(v\) and nonzero on \(u\) refutes (12). Otherwise \(u=\mu v\) for a nonzero \(\mu\in F\), since the cut assumption made both tensors nonzero. The elements \(g_1=\mu x_1\) and \(g_i=x_i\) for \(i>1\) give an actual transporter in the original bases. This proves completeness and, in particular, existence of a geometric transporter on the recognized class implies existence of a transporter over the base field.

## 3. Size and generation of the certificates

For a stored PC equation \(P=0\), a product by a polynomial \(Q\) means expand \(Q\), multiply \(P\) by each monomial by consecutive single-variable multiplications, and add the resulting equations with scalar coefficients. It is valid to retain all earlier equations for reuse. Tensor-algebra multiplication, projection, and base changes on coordinate arrays use constant coefficient tables. In a product difference, each telescope term is one previously derived equation times the product of unchanged entries in the other positions. In (4)–(12) a multiplied term uses only an absolute bounded number of variable entries from each mode. Each contraction or Kronecker operation sums over \(O(d)\) indices, with at most a constant number of length-\(n\) indices per mode. The algebras \(K_i,K,L_i\) have dimensions \(n,n^d,n^{d+1}\), respectively. A generic sparse expansion of any polynomial with bounded degree per mode has \(n^{O(d)}\) possible monomials, since each mode has \(2n^2\) variables. All line counts and coefficient expansions above are polynomial in these bounds. Scalar linear row reduction also has polynomial replay cost, including the calculation of a line combination producing a nonzero constant. This proves the claimed ordinary PC sparse size. The largest degree in the construction is \(8d\) in Section 1.

A static Nullstellensatz identity follows by recording the coefficient of every original axiom in each derived coordinate. There are only an absolute bounded number of sequential stages that multiply an ideal consequence by a nonconstant polynomial. They are the cut inverse construction, the contractions, the mode normalization, the support and overlap projections, and the final scalar elimination. Within a stage each nonconstant product is a local telescope using a previously available coordinate, so the number of factors from each mode in that product is absolutely bounded. Gaussian elimination and repeated powers of constant operator matrices use only constant coefficients. Consequently the coefficient annotation keeps the total degree per mode absolutely bounded, even after multiplication by the original axiom. Coefficient vectors and the number of original axioms have \(n^{O(d)}\) expanded size. Since the last annotated line is \(1\), this is the stated sparse Nullstellensatz identity. Construction of either proof over explicit finite fields uses only arithmetic, deterministic module isomorphism, or polynomial gcds and linear algebra, all of polynomial bit cost. [Ordinary PC conventions and questions about degree and sparse size](https://arxiv.org/html/2305.19320#S7)

## 4. The density bound

The earlier sparse formal witness \(T_0\) has an invertible weighted permutation cut with \(n^h\) support tuples. Each fixed coordinate value in a mode occurs in exactly \(n^{h-1}\) support tuples. Its mode covariants are diagonal and have simple spectrum over the rational function field of the weights. Given two labels in one mode, some common context is at Hamming distance at least two from the support for both labels. For each label, at most \(n^h+(d-1)(n-1)n^{h-1}\) contexts are within distance one. The union for two labels has fewer than \(n^{d-1}\) members when \(n\ge37\) and \(d=2h\ge4\).

Perturb \(T_0\) by \(\tau Z\) with algebraically independent entries in \(Z\). The simple eigenvalues and eigenvectors lift over formal power series in \(\tau\), in bases reducing to the original bases at \(\tau=0\). To obtain such bases, lift each simple characteristic root using its nonzero derivative and solve the eigenvector system with its designated original component equal to one. In a position at Hamming distance at least two from the old support, the first-order frame changes of \(T_0\) vanish, since one first-order change can alter at most one slot. Its first-order entry in the lifted frames is therefore the corresponding entry of \(Z\). Hence each mode graph is complete on the perturbation. This supplies a nonzero witness for all mode rank tests in every characteristic.

Write \(m=n^h\) and \(s=4m\). Use the denominator-cleared operator \(P_i=\det(M)^4 A_i\) of polynomial degree at most \(s\), and cyclic chart matrices \((w,P_iw,\ldots,P_i^{n-1}w)\) with \(w\) the all-ones vector. Their determinants have degrees at most \(J=sn(n-1)/2\) and are nonzero at \(T_0\) by Vandermonde. In the cyclic charts each coordinate of \(t\) has numerator degree at most \(dJ+1\) over the product of those determinants. The coefficients of the characteristic polynomials of \(P_i\) have degrees at most \(ns\). To form (9), exponents before reduction are at most \(2(n-1)\) in each of \(d+1\) slots. Reduction by the monic characteristic polynomials takes at most \(n\) substitutions in each slot along a monomial branch. After clearing the squared chart denominator, entries of (9) therefore have degree at most \(2(dJ+1)+(d+1)n^2s\). Take one nonzero minor of size \(n-1\) in each mode, and multiply them by all chart determinants, the balanced cut determinant, and all mode discriminants. This polynomial is nonzero by the formal perturbation. Its total degree is bounded by
\[
 m+dJ+ds n(n-1)
 + d(n-1)\big[2(dJ+1)+(d+1)n^2s\big]
 \ \le\ 32d^2 n^{h+3}.
\]
Its nonvanishing suffices for all recognition tests, so the polynomial zero bound establishes the claimed density. This is a growing-field guarantee. The algorithm on any accepted input remains exact even when the density estimate is vacuous. [Earlier weighted permutation witness](https://github.com/Dugongue/MathProofs/blob/main/GenericOrdinaryFourTI/PROOF.md) · [Schwartz, probabilistic verification of polynomial identities](https://doi.org/10.1145/322217.322225)

## 5. Transfer to literal ordinary three-tensor equations

**Theorem 2.** There is a uniform polynomial-time compilation from the preceding even-order pairs to pairs of ordinary three-tensors. The source and target transporters project and lift over the base field and every extension. On negative inputs of the recognized source class the literal cubic action and two-sided inverse equations of the compiled pair have ordinary PC refutations of degree \(O(d)\) and expanded size polynomial in the compiled side length. The field equations remain absent. For order four the degree bound is absolute. For variable order the degree is \(O(\log(r+1))\), where \(r\) may be the ordinary rank or border rank of either compiled tensor.

Introduce a pair of tensor-product trees for the two halves of the balanced cut. Each leaf has its \(n\)-dimensional input mode space. Take the right half spaces with the dual convention so the input tensor is the constant matrix \(M\) of a linear map from the right root space to the left root space. Each interior tree node has the based tensor product of its two children as its space. The dimensions at the roots are \(n^h\). For every node \(j\) with space \(W_j\), use three named copies \(W_j^X,W_j^Y,W_j^Z\) in a bilinear table. There are additional one-dimensional named blocks \(Fx_0,Fy_0,Fy_*,Fz_0\). Put in the table
\[
 x_0y_0=x_0y_*=z_0,\qquad
 (w^X)y_0=w^Z,\qquad x_0(w^Y)=w^Z
\]
for each node. For each pair of children \(i,j\) with parent \(k\), use the based product \(W_i^X\times W_j^Y\to W_k^Z\), \(x,y\mapsto x\otimes y\). Finally use \(W_{\rm right}^X\times Fy_*\to W_{\rm left}^Z\) with matrix \(M\). The target table uses the same blocks and fixed products, with \(N\) in place of \(M\). All unlisted products are zero.

Let \(a,b\) be the scalar maps on \(x_0,y_0\) in a block-preserving witness, with designated inverses. The first two scalar products force \(ab\) on \(z_0\) and \(b\) on \(y_*\). If \(P_j,Q_j,R_j\) are the maps on a node's three copies, the two identity products give \(R_j=bP_j=aQ_j\). Normalize \(g_j=a^{-1}P_j\), with inverse map \(g_j'=aP_j'\). These are monomials of degree two in the block variables, with \(a^{-1}\) the supplied inverse coordinate. The table therefore gives the equations
\[
 g_k=g_i\otimes g_j,\qquad g_{\rm left} M=N g_{\rm right}.
\tag{13}
\]
One obtains them in bounded-degree PC by replacing each of the local factors and using the scalar inverse axioms. Conversely every tensor witness lifts by taking the tensor-product node maps and setting the anchor scalars to one.

On the left leaves read the ordinary modes as \(g_i\), and on the right leaves read them as \(g_i'^{\mathsf T}\). Their designated inverse matrices are read with the reverse choices. By induction on each tree, replace the parent variables of (13) by the Kronecker products of the corresponding leaf maps. Every new coordinate equation \(g_k-\bigotimes_{\text{leaves below }k}g_i=0\) is obtained by replacing the two child factors in its parent equation. If a child has \(e\) leaves, its expanded product degree is \(2e\) and each entry is one monomial. Thus the largest intermediate degree is \(O(d)\) and the sparse cost is polynomial in the node dimensions and \(n^d\). Apply the root equations and multiply by the Kronecker product of inverse leaves on the right, canceling each pair with the leaf inverse equations. This prepares precisely the substituted original \(d\)-tensor action equations, as well as their two-sided inverse equations. Each original variable maps to a single degree-two monomial in the labelled proof. Replay any proof from Theorem 1 after preparation, replacing multiplication by an original variable by two ordinary multiplications. Sparsity is preserved up to polynomial overhead.

Finally apply the earlier sparse ordered-path erasure compiler to the named bilinear table. The compiler outputs the same-format ordinary multiplication tensors of two unital triangular algebras. Its ordinary-to-labelled readout of each block witness entry is a single degree-three monomial, and its axiom preparation has constant degree and polynomial sparse size. Thus replaying the labelled proof gives the claimed ordinary cubic proof. The compiled common side \(N_0\) is at least \(n^h\) and at most \(O(d n^h)\), since the tree has \(O(d)\) nodes and no node has dimension greater than \(n^h\). Evaluation of the multiplication tensor at the algebra unit gives a flattening of rank \(N_0\), so its tensor rank and border rank are at least \(N_0\). Therefore \(d=2h=O(\log(r+1))\). The average-case interpretation is the distribution obtained by compiling uniform even-order inputs, with the original density bound. [Ordered-path erasure and monomial proof transfer, Theorem A](https://github.com/Dugongue/MathProofs/blob/main/OrdinaryTensorTransferFallout/Mixed.md)

The paper's Open Questions 7.1 and 7.2 ask for general rank-degree and sparse-size bounds for ordinary three-tensor nonisomorphism. Theorem 2 gives both bounds on the stated compiled class. Theorem 1 applies directly to the original even-order encoding and its arbitrary target. Exact finite arithmetic checks covered 512 instances of (4) with arbitrary witness matrices and 331 split overlap comparisons against exhaustive unit-tuple search, including 112 positive and 219 negative cases. The proofs are written arguments, and publication priority for the proof-complexity claims is provisional. [Galesi–Grochow–Pitassi–She, §7](https://arxiv.org/html/2305.19320#S7)
