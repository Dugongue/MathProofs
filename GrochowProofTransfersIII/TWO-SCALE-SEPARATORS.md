# Polynomial separators from two infinitesimal scales

Let \(G\subseteq\mathrm{GL}_n(\mathbb C)\) be a matrix Lie group. Suppose its real Lie algebra contains matrices \(T_1,\dots,T_d\) that are linearly independent over \(\mathbb C\). This holds with \(d=n^2\) in both \(U_n\) and \(\mathrm{GL}_n(\mathbb R)\).

**Theorem.** For any integers \(h_X,h_Y,h_Z\ge2\), there are one-parameter sets in \(G\) with the triple-product property for every sufficiently small positive \(\epsilon\), of sizes \(h_X^d,h_Y^d,h_Z^d\). They have holomorphic border-separating polynomials in the entries of \(G\) of degree at most
\[
d\big((2h_Y-1)h_Xh_Z-1\big).
\]
In particular, taking \(h_X=h_Y=h_Z=\lceil q^{1/3}\rceil\) gives sets of size at least \(q^{n^2/3}\) with degree \(O_n(q)\) in either of the two groups above. The explicit degree bound is sharp on the diagonal unitary torus for the corresponding grids with \(d=n\).

## Triple-product property

For a real vector \(a\) write \(A(a)=\sum_i a_iT_i\). Use independent box labels
\[
 a\in\{0,\ldots,h_X-1\}^d,\qquad
 b\in\{0,\ldots,h_Y-1\}^d,\qquad
 c\in\{0,\ldots,h_Z-1\}^d
\]
and define
\[
 x_a=\exp(\epsilon^2 A(a)),\qquad
 y_b=\exp(\epsilon A(b)),\qquad
 z_c=\exp(\epsilon^2 h_X A(c)).
\]
These curves lie in \(G\). Each indexing is injective for all sufficiently small positive \(\epsilon\): its first nonzero leading difference is the scalar multiple of a nonzero difference of label matrices. All comparisons are among finitely many analytic curves, so a common positive interval works for every label.

In an identity \(x_a^{-1}x_{a'}y_b^{-1}y_{b'}z_c^{-1}z_{c'}=I\), the first-order term is \(A(b'-b)\). Thus unequal \(b,b'\) cannot occur for sufficiently small positive \(\epsilon\). When \(b=b'\), those factors cancel exactly. The second-order term of the remaining product is \(A(a'-a+h_X(c'-c))\). A difference of \(a\)-labels has every coordinate of absolute value less than \(h_X\). Thus this term can vanish only when \(a=a'\) and \(c=c'\). This proves the triple-product property, with the same finite uniform-endpoint argument.

## Border-separating polynomials

Take complex-linear functionals \(\ell_i\) on the full matrix space satisfying \(\ell_i(T_j)=\delta_{ij}\). Let \(p(t)\) be the Lagrange selector equal to one at zero and zero on all other integers in \([1-h_Y,h_Y-1]\). Its degree is \(2h_Y-2\). Define
\[
D=h_Xh_Z-1,\qquad
W=\{-h_X(h_Z-1),\ldots,h_X-1\}.
\]
The integer \(a_i-h_Xc_i\) determines \((a_i,c_i)\) and attains every element of \(W\). For \(w\in W\) let \(r_w\) be the Lagrange selector supported at \(w\) on \(W\), of degree \(D\).

For target \((a,c)\) put \(w_i=a_i-h_Xc_i\) and use the polynomial
\[
 P_{a,c}(g,\epsilon)=\prod_{i=1}^d
  p\left(\frac{\ell_i(g-I)}{\epsilon}\right)^{D+1}
  r_{w_i}\left(\frac{\ell_i(g-I)}{\epsilon^2}\right).
\]
Its coefficients are Laurent polynomials in \(\epsilon\), so they have the required analytic dependence for positive \(\epsilon\). Its degree in matrix entries is at most \(d((D+1)(2h_Y-2)+D)\).

For
\[
g=x_{a'}y_b^{-1}y_{b'}z_{c'}^{-1}
\]
write \(\beta_i=b'_i-b_i\). Always \(\ell_i(g-I)=\epsilon\beta_i+O(\epsilon^2)\). If \(\beta_i\ne0\), the first selector is \(O(\epsilon)\), and the second is \(O(\epsilon^{-D})\). Their product with the displayed power is \(O(\epsilon)\). If \(\beta_i=0\), the first selector is \(1+O(\epsilon)\), and its companion is bounded since its argument is \(O(1)\). Thus any unequal middle pair makes the whole product \(O(\epsilon)\), with no pole at the other coordinates.

If \(b=b'\), then \(g=x_{a'}z_{c'}^{-1}\), and
\[
\ell_i(g-I)=\epsilon^2(a'_i-h_Xc'_i)+O(\epsilon^4).
\]
All first selectors tend to one. The second selectors together equal \(\mathbf{1}_{(a',c')=(a,c)}+O(\epsilon)\). This is exactly the border-separating property for the product support \(XY^{-1}YZ^{-1}\) and the desired outputs \(XZ^{-1}\). Each estimate is uniform on the finite support for the fixed grid sizes.

For \(U_n\), take a real basis of the skew-Hermitian matrices. It is complex-linearly independent: a complex relation \(A+iB=0\) with \(A,B\) skew-Hermitian forces \(A=0\) because \(iB\) is Hermitian, and then \(B=0\). For \(\mathrm{GL}_n(\mathbb R)\), use the matrix units. These give the asserted full \(d=n^2\).

## Sharpness on a diagonal torus

Take \(G=U_1^d\) diagonal, with basis matrices \(i E_{jj}\). The one-coordinate support consists of
\[
s_{b,w}(\epsilon)=\exp(i(\epsilon b+\epsilon^2 w)),
\qquad b\in[1-h_Y,h_Y-1]\cap\mathbb Z,\quad w\in W .
\]
All combinations occur and the points are distinct for small positive \(\epsilon\). Set \(v=(2h_Y-1)h_Xh_Z\). For each support point \(s\) let
\[
\lambda_s=\Big(\prod_{s'\ne s}(s-s')\Big)^{-1}.
\]
The leading coefficient in Lagrange interpolation gives \(\sum_s\lambda_s s^k=0\) for every \(k<v-1\). Within a fixed first-order cluster \(b\), every difference has order two, and all differences between distinct clusters have order one. Each cluster has the same size \(h_Xh_Z\). Therefore all the \(\lambda_s\) have the same pole order and any ratio to one of them converges to a finite nonzero value.

A polynomial in the diagonal entries of degree below \(d(v-1)\) is killed by the evaluation functional given by the tensor product of these one-coordinate weights. Indeed each of its monomials has degree below \(v-1\) in some coordinate. This holds for each small \(\epsilon>0\), also for Laurent-dependent coefficients. Divide the functional by its weight at the desired output (the clean cluster \(b=0\) in each coordinate). Each resulting weight stays bounded. If such a polynomial were a border separator, the functional would tend to one because the target value tends to one and every other value is \(O(\epsilon)\). This contradicts its vanishing. The construction attains the resulting minimum degree.

## Comparison and verification

Definition 2.5 of [Blasiak, Cohn, Grochow, Pratt and Umans](https://arxiv.org/html/2410.14905#S2.SS2) uses exactly the support and \(1+O(\epsilon)\) versus \(O(\epsilon)\) limits checked above. Their Theorem C summary reports size \(q^{n^2/4-n/4}\) at degree \(O_n(q)\), while the detailed Theorem 3.1 states \(q^{n^2/4-n/2}\) for its displayed special-unitary construction. The finite grids here give a larger exponent than either displayed bound at degree \(O_n(q)\). The cited paper also studies continuous submanifold constructions. The finite grid result makes no assertion about their dimensions. It is a direct construction in \(U_n\) and \(\mathrm{GL}_n(\mathbb R)\), and its proof needs no invariant polynomial on the entire group. The exponent \(n^2/3\) remains below the \(n^2/2-o(n)\) sufficient size criterion in their Corollary 2.8. This is a separator-size theorem, with no new bound on the unrestricted exponent of matrix multiplication.

The proof uses the separation of scales in [Davis and GPT-6.2 Astra’s two-speed insertion argument](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/lonely-runner-two-insertions/PROOF.md) as a design cue. That argument controls a faster phase on a surviving interval before using an exact local witness. Here the order-one difference is detected before decoding the order-two coordinates. The local rejection step is analogous to the boundary-conditioned certificate in their [Frankl proof](https://github.com/1337isnot1337/solved-conjectures/blob/892c04046aadc8731dd510bb9c9b3ca1a086bae1/results/frankl-generator-families/PROOF.md): test the coarse trace before applying the finer rule. No statement of either upstream proof is an assumption of this theorem.

The Lean companion checks the scalar interpolation selectors and both exact numerator congruences. The Python replay uses exact arithmetic for finite Laurent-series controls and the torus degree witness. The analytic Lie group theorem and comparison are given by the written argument. Publication priority remains provisional.

## A one-rate grid control

The same cardinality and degree follow from a direct mixed-radix construction. Replace the exponents of \(x,y,z\) by \(\epsilon A(a),\epsilon h_Xh_Z A(b),\epsilon h_X A(c)\), respectively. Write \(M=h_Xh_Z\). The leading coordinate in the separator's product order is \(a_i-h_Xc_i+M(b'_i-b_i)\). Each difference \(b'_i-b_i\) gives a different translate by \(M\) of the interval \(W\) of length \(M\). These translates partition a contiguous integer interval of length \((2h_Y-1)M\). Ordinary Lagrange selectors on this larger interval, evaluated at \(\ell_i(g-I)/\epsilon\), isolate the clean target with degree \(d((2h_Y-1)M-1)\).

In the triple-product order the leading coordinate is \(a'_i-a_i+h_X(c'_i-c_i)+M(b'_i-b_i)\). The first two differences sum to an integer of absolute value at most \(M-1\). Thus a zero leading vector forces \(b=b'\) and then forces \(a=a'\), \(c=c'\). Both orders of products are covered for small positive \(\epsilon\). This control shows that the larger cardinality can already be obtained in the tangent-grid model. The two-scale construction gives the same bound while separating the two different orders explicitly. The conclusion is about separators in the stated matrix groups and degree model.
