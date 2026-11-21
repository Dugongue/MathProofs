# First syzygies and a parity extension for ternary symmetric bimaps

Work over \(F=\mathbb F_3\). A symmetric bimap \(\beta:X\times X\to Z\) has an induced map \(b: \operatorname{Sym}^2X\to Z\). Assume \(b\) surjective. The bases of \(X,Z\) are part of the input. A transporter \((g,h)\) satisfies \(h\beta(x,y)=\beta'(gx,gy)\). Put \(K=\ker b\), and define the first multiplication map and its two defects by
\[
 m:X\otimes K\longrightarrow\operatorname{Sym}^3X,\quad x\otimes q\longmapsto xq,\qquad
 S=\ker m,\quad C=\operatorname{coker} m.
\]

**Theorem.** Fix \(c>0\) and let \(L\) be dense input length. When \(n=\dim X\) is odd, \(\dim K+\binom{n+2}{2}\) is even, and \(\dim S,\dim C\le c\log_2(2+L)\), prescribing the label determinant \(\det h\) reduces to one ordinary three-tensor isomorphism instance over \(F\). If \(m\) is an isomorphism, the determinant constraint is a comparison of two directly computed nonzero scalars before the ordinary instance, and the parity condition is automatic.

There is also a polynomial-time recognizable even-ambient, odd-label, scalar-centroid class on which the **combined** character \(\det g\det h\) reduces to one ordinary TI instance. It is obtained by a one-variable square-zero extension of the odd-ambient case, with the old variables recognized from the centroid of a dual kernel bimap. Both ambient and label dimensions in this class grow unboundedly. An elementary sampling argument below constructs arbitrarily large instances over \(F\), with polynomial verification and expected polynomial generation time. The class includes ordinarily equivalent pairs excluded by the prescribed combined character.

## 1. The raw determinant formula

Put \(k=\dim K\) and \(b_3=\binom{n+2}{2}\). The induced map \(g_K\) on the kernel is the restriction of \(\operatorname{Sym}^2g\). The determinants on the symmetric powers are \((\det g)^{n+1}\) and \((\det g)^{b_3}\) in degrees two and three. For example this follows by triangularizing over an algebraic closure and multiplying diagonal monomials, so it also holds in characteristic three.

For calibration choose a basis of \(K\), followed by lifts of the written basis of \(Z\), in \(\operatorname{Sym}^2 X\). Denote its change-of-basis determinant from the raw monomial basis by \(d_X\), with the direction being the adapted basis columns written in raw coordinates. This gives
\[
 \det h=(d_X/d_Y)(\det g)^{n+1}(\det g_K)^{-1}
\]
for a transporter from \(X\) to the primed instance, here denoted \(Y\).

For \(m\), choose frames of its kernel, image and cokernel. Concatenate the kernel frame with lifts of the image frame in the domain, and concatenate the image frame with lifts of the cokernel frame in the codomain. Write \(a_X\) and \(b_X\) for these two adapted-to-raw basis determinants, respectively. Use analogous definitions at \(Y\). Since the induced image determinant cancels between the two exact sequences, one obtains
\[
 (\det g)^k(\det g_K)^n(\det g)^{-b_3}
   =\frac{(a_Y/b_Y)}{(a_X/b_X)}\,\frac{\det g_S}{\det g_C}.
\]
Every nonzero scalar of \(F\) is its own inverse. For odd \(n\), this gives
\[
 \det h=\frac{\eta_Y}{\eta_X}(\det g)^{k+b_3}\det g_S\det g_C,
 \qquad \eta_X=\frac{a_X}{b_Xd_X}.
\tag{1}
\]
All the calibrations are computed by linear algebra at each endpoint. When \(m\) is an isomorphism, \(nk=\binom{n+2}{3}\), hence \(b_3=3k\) and \(k+b_3=4k\). The right side of (1) is then just \(\eta_Y/\eta_X\). For even \(n\), the same exact sequence controls \((\det g)^{k+b_3}\), with the kernel determinant cancelling from that identity. The square-zero extension below transfers precisely the odd-dimensional label test to the even-dimensional combined test.

The two defect dimensions and all spaces in the construction are intrinsic. A mismatch between their dimensions at the endpoints excludes isomorphism. To describe the determinant in a tensor system, include \(\beta\), the truncated symmetric algebra on \(X\) through degree three, and the degree-one embedding of \(X\) and degree-two and degree-three inclusions. This algebra is generated in degree one, so the actions in degrees two and three are forced. Link \(K\) by inclusion, link \(X\otimes K\) by the bilinear tensor-product map, and include \(m\), the kernel inclusion, and the cokernel quotient. All maps on \(S,C\) are now exactly those of the same transporter. Include the exterior algebras of the two defect spaces with their degree-one and top-line inclusions. They have dimensions \(2^{\dim S}\) and \(2^{\dim C}\). Use bilinear multiplication of their two top-line scalars with the respective endpoint calibrations \(\eta_X,\eta_Y\) to force (1) on a new line, and pin the line to the desired label determinant. A zero-dimensional contribution is a pinned neutral line. These are constantly many tensor records of polynomial dimension. Every comparison of the records has the stated sign on the same bimap witness, and every such witness extends. Applying the same-field compiler gives one ordinary instance. [Tensor-system compiler, Chen–Grochow–Qiao–Tang–Zhang](https://arxiv.org/html/2306.03135v2#S4)

## 2. Even ambient dimension and odd label dimension

Let the odd-dimensional base bimap have zero common radical. Set \(U=X\oplus Fe\) and \(W=Z\oplus X_c\), where \(X_c\) is another copy of \(X\). Define
\[
 \widehat\beta(x+ae,y+be)=(\beta(x,y),\, ay+bx).
\tag{2}
\]
Thus \(e^2\) is zero. Its symmetric kernel is \(\widehat K=K\oplus Fe^2\). It is surjective since the first block is spanned by the old products and all cross labels occur. Its common radical is zero: contraction by \(e\) first kills the \(X\) component, and contraction by \(X\) then kills the \(e\) component.

In fact the new centroid is scalar. Let \(A\) be any operator on \(U\) satisfying \(\widehat\beta(Au,v)=\widehat\beta(u,Av)\), and write the \(e\)-component on \(X\) as \(\ell(x)\). The equation on \(X\times X\) gives \(\ell(x)y=\ell(y)x\); as \(\dim X\ge2\), this forces \(\ell=0\). Write \(Ae=u+\gamma e\). The equation on \(X\times e\) gives \(A|_X=\gamma I_X\) from the cross labels and \(\beta(x,u)=0\) for all \(x\) from the old labels. Thus \(u=0\). For a centroid pair its label operator is then the same scalar by surjectivity.

### Recover the splitting on the raw input

The input need not give the split \(U=X\oplus Fe\). From its raw kernel \(\widehat K\) form the dual bimap
\[
 \kappa:U^*\times U^*\longrightarrow \widehat K^*
\]
by evaluating the symmetric polarizations of the quadrics in \(\widehat K\). Use the normalization that \(v^2\) evaluates as \((\lambda,\mu)\mapsto\lambda(v)\mu(v)\). This bimap is surjective and is functorial under every original transporter, using the inverse-dual maps on \(U\) and \(\widehat K\). For (2) it is the orthogonal direct sum of the bimap of \(K\) on \(X^*\) and the one-dimensional square bimap on \((Fe)^*\).

Require \(\kappa\) to have zero common radical, and compute its centroid by linear equations. It is a commutative algebra in its faithful action. Closure follows by moving the operators across the two arguments, and commutativity is seen by evaluating a product of two operators in either order on distinct arguments and using surjectivity and zero common radical. Its cube-fixed ring is a product of copies of \(F\), one per primitive local factor. Indeed sufficiently high cube powers kill the nilradical and are bijective on the product of finite residue fields, so the stable image gives the coefficient fields, in which the cube-fixed elements are the prime-field scalars. Compute the cube-fixed space by a linear kernel, and separate its primitive idempotents using the indicators \(1-(a-u)^2\) for a basis element \(a\) and \(u\in F\). Refining the idempotent slots this way is polynomial-time, since a basis separates all the factors and the number of nonzero slots is bounded by the dimension. [Wilson, centroid decomposition of bimaps](https://arxiv.org/abs/1005.0548) [Earlier centroid recovery](CentroidDeterminantDescentSeed.md)

Require exactly one primitive input projection of dimension one. Its range and complementary range in \(U^*\) recover the two primal spaces by taking their respective complementary annihilators. Write them as \(E\) of dimension one and \(X\) of dimension \(n\). Verify
\[
 \widehat K=(\widehat K\cap\operatorname{Sym}^2 X)\oplus\operatorname{Sym}^2 E
\]
and that the recovered base bimap to \(Z=\widehat\beta(X,X)\) passes the odd-dimensional theorem, including zero common radical. These are all deterministic linear algebra checks apart from the explicitly described centroid computations. The kernel condition gives the form (2) in the induced cross-label frame. Every transporter must preserve the displayed splitting because it is obtained by a unique primitive projection.

The recovery hypotheses hold for (2) whenever \(K\) has full contraction support \(X\) and contains no nonzero square. Full support makes the radical of the dual bimap of \(K\) zero. A one-dimensional primitive factor in that bimap would give an orthogonal direct summand with a one-dimensional output. A functional on that output extended by zero to the other summands would give a nonzero multiple of a square in \(K\), a contradiction. Thus the only one-dimensional primitive input factor in \(\kappa\) is the added factor. The raw recognition procedure does not enumerate squares or solve a rank-one search problem.


### The exact character after extension

In frames adapted to (2), a transporter acts on \(X\) by \(g\), on \(E\) by \(\alpha\), on \(Z\) by \(h\), and on the cross labels by \(\alpha g\). The product equations force the last two actions, and every old transporter extends with \(\alpha=1\). Hence the combined determinant is \((\det g)\alpha(\det h)\alpha^n\det g=\det h\) over \(F\), since \(n\) is odd. At each endpoint let \(F_X\) be the product of the adapted-to-raw frame determinants on \(U,W\), using \(X,E\) on \(U\), and \(Z,\widehat\beta(e,x_i)\) on \(W\). The raw combined character is \((F_Y/F_X)\det h\). Calibrate by this known ratio and use the single ordinary comparison from (1).

For odd \(n\), \(n(n+1)/2\) and \(\binom{n+2}{2}\) have the same parity, so the parity test in (1) implies \(\dim Z\) even. The extension has \(\dim U=n+1\) even and \(\dim W=\dim Z+n\) odd. The associated cube-zero local algebra \(F1\oplus U\oplus W\) therefore has even dimension. An algebra isomorphism fixes the unit and preserves the radical and its square, so its determinant is the combined bimap character. Conversely every bimap transporter extends to the algebra. Its even dimension makes the rectangular cubic bridge preserve the combined sign. [Exact cubic orientation bridge](ExactCubicOrientationSeed.md)


## 3. A finite-field existence and sampling proof

For \(n\ge7\), \(n\equiv1,5\bmod6\), take \(k=(n+1)(n+2)/6\) independent uniform samples in \(\operatorname{Sym}^2 F^n\). The proposed multiplication map is square of size \(nk\). A nonzero linear syzygy of coefficient-matrix rank \(r\) vanishes with probability \(3^{-D_r}\), \(D_r=\binom{n+2}{3}-\binom{n-r+2}{3}\): the linear equation on the sampled coefficients has image the cubic ideal piece generated by its \(r\)-dimensional coefficient space. Counting matrices up to nonzero scalar, full rank contributes at most \(1/2\) to the union bound. The number of rank-\(r\) matrices is at most \(2\cdot3^{r(n+k-r)}\) before projectivization, from the Gaussian binomial count and \(\prod_{j\ge1}(1-3^{-j})\ge1/2\). For \(r<n\) the exponent saving is
\[
 D_r-r(n+k-r)=r(n-r)(2n-r-3)/6\ge(n-1)(n-2)/6 .
\]
The lower ranks contribute at most \((n-1)3^{-(n-1)(n-2)/6}\le6/243\).

Write \(K\) for their span and \(z=(n^2-1)/3\) for the base label dimension when the samples are independent. Invertibility forces independence. The probability that the span contains a square is at most \(3^{n-z}/2\), by counting projective vectors and nonzero linear combinations, each fixed combination being uniform. Thus simultaneous success has probability above \(0.47\). Full contraction support follows from surjectivity: containment in \(\operatorname{Sym}^2 X_0\) for proper \(X_0\) would leave the nonzero cubic quotient \(\operatorname{Sym}^3(X/X_0)\). These samples pass the raw recognizer after (2), so repetition gives expected polynomial generation time without a search for squares.


Injectivity of \(m\) also forces zero common radical and scalar centroid of the old bimap. A radical element \(x\ne0\) gives \(xX\subseteq K\), and for independent \(y,z\) the tensor \(z\otimes xy-y\otimes xz\) is a nonzero syzygy. For a balanced adjoint operator \(A\), put \(q_{xy}=A(x)y-xA(y)\in K\). Then \(zq_{xy}-yq_{xz}+xq_{yz}=0\). If any \(q_{xy}\ne0\), take \(z\) independent of \(x,y\) to obtain a nonzero syzygy. If all these quadrics vanish, comparison on basis pairs forces \(A\) scalar. In particular both bimaps in the extension construction have scalar centroid. For a base automorphism (1) has value \(1\), so every extended automorphism has combined determinant one. Reflecting one target label basis vector gives ordinary equivalence with negative combined sign for every transporter.

These are written proofs without Lean kernel verification.
