# Factoring-free transporter search for generic ordinary even-order tensors

Let \(k=\mathbb F_q\) be explicitly presented, let \(d=2h\ge4\), and let \(n\ge37\). The ordered action is that of \(\mathrm{GL}_n(k)^d\) on the dense \(d\)-tensors of side \(n\). An earlier algorithm compares such tensors via an invertible balanced cut and one simple-spectrum covariant per mode. Its growing-field acceptance bound is \(1-4d\,n^{h+2}/q\). Its arbitrary-field implementation factors univariate polynomials and constructs additive field generators, using Las Vegas time. In fixed characteristic it is already deterministic. [GenericOrdinaryFourTI, §§1–5](https://github.com/Dugongue/MathProofs/blob/main/GenericOrdinaryFourTI/PROOF.md)

**Theorem.** There is an intrinsic, polynomial-time recognizable subclass of that spectral locus with density at least
\[
1-\frac{32d^2 n^{h+3}}q .
\]
On this subclass, a first tensor can be compared to every target by a deterministic polynomial-bit-time algorithm returning an explicit ordinary transporter on a positive instance. The algorithm uses no factoring premise. The geometric ordinary stabilizer on this subclass is exactly the scalar subgroup \(\{(\lambda_i I):\prod_i\lambda_i=1\}\). A comparison with any prescribed nonzero determinant in each mode is also deterministic polynomial time for decision and exact counting, and yields an actual transporter in deterministic quasipolynomial time under complete deterministic quasipolynomial factoring. These bounds take the full dense tensor length and \(\log q\) as input parameters, including when \(d\) varies.

On the entire previously recognized class, including every support pattern, the earlier ordinary **decision** algorithm is deterministic quasipolynomial under that same factoring premise and retains its original density. Below we give a different, unconditional algorithm that also finds witnesses on the new, growing-field subclass.

## 1. Recognizing geometric support connectivity by linear algebra

Write \(T\) as a vector in \(\bigotimes_{i=1}^d V_i\). Use the covariants \(A_i(T)\) from the earlier algorithm. Each is conjugation-equivariant in its own mode, and each has squarefree characteristic polynomial \(f_i\) on the spectral locus. The algebra \(K_i=k[z_i]/(f_i)\) is finite étale. The mode \(V_i\) is a free rank-one \(K_i\)-module via \(z_i\) acting by \(A_i\). Indeed, over an algebraic closure there is one eigenline at each geometric character. Over \(k\), this implies that the minimal polynomial equals \(f_i\), so a cyclic basis exists. An explicit identification \(K_i\simeq V_i\) is computed by constructive module isomorphism for the two multiplication matrices, using the companion matrix on \(K_i\). This is deterministic polynomial time over finite fields. No irreducible factors or eigenvalues are needed by the algorithm. [Brooksbank–Luks, Testing isomorphism of modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Write \(T\) as \(t\) in the product algebra \(K=\bigotimes_i K_i\) using those identifications. In split coordinates over \(\bar k\), write \(t_{a,c}\) for a coordinate with index \(a\) in mode \(i\) and context \(c\) in all other modes. Define a graph on the \(n\) geometric characters of \(K_i\) by joining \(a,b\) if there is a context \(c\) with \(t_{a,c}t_{b,c}\ne0\). The class requires this graph to be connected for every \(i\). Different cyclic generators multiply all coordinates by products of nonzero coefficients. Ordering eigenvalues only permutes the vertices. The definition is thus intrinsic and invariant under ordered tensor isomorphism.

The connectivity test itself never passes to a splitting field. For each mode, let
\[
L_i=K_i\otimes K_i\otimes\bigotimes_{j\ne i}K_j
\]
and use superscripts \((1),(2)\) for the two maps \(K\to L_i\) that use the first or second copy of \(K_i\), respectively, and share all other factors. The analogous maps \(K_i\to L_i\) are denoted in the same way. Compute the kernel of
\[
x\longmapsto t^{(1)}t^{(2)}(x^{(1)}-x^{(2)}).
\tag{1}
\]
Over \(\bar k\), it imposes exactly \(x_a=x_b\) on the edges. Consequently its dimension is the number of connected components, including isolated vertices. Ranks and nullities of linear maps commute with base change. The recognizer is that every kernel in (1) has dimension one. The largest algebra used here has dimension \(n^{d+1}\), which is polynomial in the dense input size \(n^d\).

## 2. Exact witness recovery on the connected class

If the target fails the spectral tests or its mode characteristic polynomials differ from those of the source, reject by equivariance. Otherwise put both tensors in the same model \(K\) by their independently computed cyclic bases, and denote the target by \(u\). A genuine transporter between the two arrays must intertwine the mode covariants. Therefore the remaining maps are precisely multiplication by \(g_i\in K_i^\times\), and the target equation is
\[
u=(\bigotimes_i g_i)t.
\tag{2}
\]
For each \(i\), solve the \(k\)-linear equation in \(L_i\)
\[
u^{(1)}t^{(2)}x^{(2)}-u^{(2)}t^{(1)}x^{(1)}=0 .
\tag{3}
\]
If (2) has a solution, then over \(\bar k\), for every common context of two support entries, (3) gives \(x_a/g_{i,a}=x_b/g_{i,b}\). The omitted context factors are units and cancel. For the remaining coordinates (3) imposes nothing. Connectivity gives a one-dimensional kernel, spanned over the base field by \(g_i\). Thus reject unless each kernel is a line with an invertible basis element \(x_i\) in its \(K_i\). Test invertibility by its multiplication matrix. Compute \(v=(\bigotimes_i x_i)t\). Accept precisely if \(u=\lambda v\) for some \(\lambda\in k^\times\), which is checked by comparing coordinates over \(k\). On acceptance absorb \(\lambda\) in the first mode and return the actual mode maps in the input bases. Conversely a true witness survives every test, since the basis elements \(x_i\) differ from it only by nonzero scalars. The same argument with the source as target proves the exact geometric stabilizer claim.

For prescribed determinants \(D_i\in k^\times\), take one ordinary witness \((G_i)\) and write \(a_i=D_i/\det G_i\). All other witnesses are obtained using the scalar stabilizer. The requirements are \(a_i=\lambda_i^n\) with \(\prod_i\lambda_i=1\). These are feasible exactly when \(\prod_i a_i=1\) and all \(a_i^{(q-1)/g}=1\), where \(g=\gcd(n,q-1)\). Necessity is direct. For sufficiency choose independently \(n\)-th roots for the first \(d-1\) values and use the inverse product for the final root. Each of the first choices has exactly \(g\) possibilities, so the exact count is \(g^{d-1}\) when feasible and zero otherwise. The ordinary count is \((q-1)^{d-1}\). Quasipolynomial factoring is needed only for constructing the prescribed-determinant witness by degree-\(n\) binomial calls. The membership tests and counts use just powers and gcds.

## 3. Geometric witness and quantitative average-case coverage

We use the sparse formal witness \(T_0\) from the earlier spectral result. It is a weighted permutation tensor for the balanced cut. Its weights are independent, and all \(d\) covariants are diagonal with distinct entries over the rational function field of those weights, in every characteristic. Its support has \(n^h\) tuples, and each individual coordinate value in any mode belongs to exactly \(n^{h-1}\) of them. These cardinalities follow because the input and output index tuples each occur exactly once in that permutation. The earlier construction of \(T_0\) works for every \(n\ge37\) and is stated directly for \(d=2h\). [GenericOrdinaryFourTI, sparse witness and extension to even orders](https://github.com/Dugongue/MathProofs/blob/main/GenericOrdinaryFourTI/PROOF.md)

For two distinct labels \(a,b\) in a mode, there is a context \(c\) such that both tuples \((a,c)\) and \((b,c)\) have Hamming distance at least two from the support of \(T_0\). For a fixed mode label, at most \(n^h\) contexts are forbidden by a tuple agreeing on all other modes. Another at most \((d-1)(n-1)n^{h-1}\) contexts are forbidden by changing an index in a different mode of a support tuple with that fixed label. So two labels forbid at most \(2d n^h\) contexts, and \(n^{d-1}>2d n^h\) for the stated parameters.

Form \(T(t)=T_0+tZ\) with all coordinates of \(Z\) algebraically independent over the weight field. Its cut remains invertible over the field of formal Laurent series in \(t\). Its covariants admit eigenbases reducing to the standard basis at \(t=0\). To see this, lift each simple root of the characteristic polynomial recursively in \(t\), using the nonzero derivative at the constant term. Solve the eigenvector equations with the corresponding component normalized to one. The complementary block is invertible modulo \(t\), so it determines the lift. The resulting diagonalization is over the same formal power series ring. For any tuple at Hamming distance at least two from the original support, its coefficient in the tensor expressed in these eigenbases has first-order term \(tZ_{a,c}\). A first-order change of frames acts on only one slot of \(T_0\), which gives zero at that tuple by its distance. Thus the context just chosen witnesses an edge between \(a,b\) in the support graph of the formal perturbation. Each mode graph is even complete. This supplies a nonvanishing witness for the linear rank tests without assuming algebraic independence of the eigenvectors and the tensor.

For the explicit density bound set \(m=n^h\), and let \(D\) be the determinant of the balanced cut. Use denominator-cleared operators \(P_i=D^4 A_i\) of degree at most \(s=4m\) in the tensor coordinates, as in the earlier contraction. Multiplying operators by nonzero scalars leaves the geometric support in their spectral frames unchanged. On a rational coordinate chart use the fixed all-ones vector in each mode and form the matrix \(C_i\) with columns \(v_i,P_i v_i,\ldots,P_i^{n-1}v_i\). Each determinant has degree at most \(J=sn(n-1)/2\). These matrices are invertible at \(T_0\), by a Vandermonde determinant, and hence at the formal perturbation. With common denominator \(\prod_i\det C_i\), all coordinates of \(t\) have numerators of degree at most \(dJ+1\).

Use the characteristic polynomials of the \(P_i\) to compute the matrix in (1) on that chart. Their coefficients have degrees at most \(ns\). Before reduction, the power exponents in a product in (1), on input a basis element, are at most \(2(n-1)\) in each slot. Reducing a monomial modulo the monic mode characteristic polynomials lowers the relevant exponent each time and uses at most \(n\) replacements in each of the \(d+1\) slots. Thus after clearing \((\prod_i\det C_i)^2\), the entries of (1) have degree at most
\[
2(dJ+1)+(d+1)n^2s.
\]
For each mode choose a nonzero minor of size \(n-1\), which exists by the formal witness. Multiply these minors by the cyclic chart determinants, \(D\), and the discriminants of the \(d\) characteristic polynomials of the \(P_i\). This gives a nonzero polynomial whose nonvanishing suffices for the recognition tests. The characteristic discriminants contribute at most \(ds n(n-1)\) in total. Hence the overall degree is at most
\[
m+dJ+ds n(n-1)+d(n-1)\bigl[2(dJ+1)+(d+1)n^2s\bigr]\ \le\ 32d^2 n^{h+3}.
\]
Although the proof of density chooses a chart and witness minors, the recognition algorithm uses the full rational linear tests in (1). The polynomial zero bound over the finite field gives the stated one-sided density. At fixed \(q\) the density estimate can be vacuous. [Schwartz, probabilistic verification of polynomial identities](https://doi.org/10.1145/322217.322225)

## 4. All support patterns under quasipolynomial factoring

In the previous algorithm the remaining decision after constructing the \(K_i\) uses their product-field decompositions and computes membership in the image of the unit map. It uses linear algebra, gcd splitting, integer normal forms and modular powering after those decompositions. Replace finite-field factorization by the deterministic quasipolynomial routine, including factors over the computed extension fields. To remove the separate random choice of an additive field generator in an explicit finite extension \(E/k\) of degree \(e\), for every \(\ell^a\parallel e\) choose \(w_\ell\) in the degree-\(\ell^a\) subfield outside its maximal proper subfield. Find both spaces by Frobenius and Gaussian elimination. The sum of the \(w_\ell\) generates \(E/k\): for each \(\ell\) the Frobenius \(q^{e/\ell}\) fixes every summand except \(w_\ell\), which it moves. Thus the sum belongs to none of the maximal proper subfields. Its minimal polynomial and coordinates are obtained by linear algebra on its powers. The same argument gives a representation over a prime field when required by the factoring routine. Degrees and bit dimensions of all these fields are polynomial in the input length. The resulting algorithm retains the earlier acceptance test and density, runs in deterministic quasipolynomial bit time, and gives a decision on that whole recognized class. The full-support subcase of §2 can also be seen directly by testing whether \(u/t\) in the product algebra is a pure tensor of units.

The algorithmic claims above are written proofs. The deterministic polynomial ordinary witness theorem and its density bound use no factoring premise. The full older spectral-locus decision bound and the determinant-constrained witness construction use the stated algorithmic input.
