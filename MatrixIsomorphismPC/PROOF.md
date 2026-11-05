# DEGREE-3 POLYNOMIAL CALCULUS REFINEMENT

Refines TRACE-CERTIFICATE.md; the frozen degree-4 Nullstellensatz certificate remains valid and unchanged.

The ordinary PC degree bound for Theorems U and C can be sharpened to 3, with the same field and input-size scope. Their explicit Nullstellensatz identities obtained by substituting source derivations still have degree at most 4. PC proof degree and the degree of the expanded Nullstellensatz certificate are different measures.

1. Choose the separating functional over the coefficient field itself.
Let B=End_Q(M directsum N) over F. Its defining intertwiner equations are F-linear, hence B tensor_F K is exactly End_Q(M_K directsum N_K) over an algebraic closure K. Pick an F-basis b_1,...,b_r of B. The affine linear constraints on a functional tau:B->F are
 tau(b_i b_j-b_j b_i)=0 for all i,j,
 tau(e-f)=1.
Section 1 of the frozen note proves this system has a solution over K (normalize its separating block trace by its nonzero value on e-f). A linear system with coefficients and right-hand sides in F that is consistent over K is consistent over F, by row reduction. Thus tau can be selected over F and normalized tau(e-f)=1. A linear extension to ambient graded matrices and both projections onto Hom spaces can also be chosen over F.

2. Prove actual linear reverse-intertwiner lines before reusing them.
For Theorem U first derive every entry of H_a=S_h N_a-M_a S_t from identity (3.1) of the frozen note. This uses intermediate polynomials of degree at most 3 and ends with the actual degree-1 polynomial H_a, not a placeholder for a cubic expression.

Now use the bilinear trace identity (2.2). Each multiplier of E or H is linear. In ordinary PC, once H_a is an available degree-1 proof line, multiplying that LINE by any proof variable gives a degree-2 line. The degree-3 intermediates in its earlier derivation remain in the proof, but they are not multiplied again. Subsequent additions also have degree at most 2. Therefore the maximum degree over the full sequential proof is 3.

For clarity, the unnecessarily looser accounting would multiply the entire earlier derivation of H by a variable, yielding a degree-4 proof. That also gives a valid upper bound and a degree-4 Nullstellensatz identity, but PC allows reusing its completed linear line directly. The degree-3 claim uses precisely that rule.

3. Congruence behaves the same way.
For every source congruence equation C_i derive the actual linear polynomials
 L_i=XA_i-B_iY^T=C_iY^T-XA_iG0^T,
 K_i=YB_i-A_iX^T=G0A_iX^T-YC_i,
and their transpose-pair versions. Each has degree-3 derivation intermediates, but its final polynomial is linear in X,Y. In the target bilinear trace identity each is multiplied by only one linear expression. Those multiplications therefore produce degree-2 PC lines and never exceed the already used degree 3. The node inverse equations are source quadratic equations or transposes. The congruence-to-transpose-pair equivalence is unchanged, including arbitrary singular/nonsymmetric labelled tuples and algebraic-closure scope.

4. Size and constructive uniformity.
Over F, the functional linear system has r<=4d^2 unknowns and at most r^2+1 constraints, all computed from an F-basis of the explicit endomorphism algebra. An F-basis and the structure constants can be found by finite linear algebra on explicit matrices. The Hom projections and residual factorizations are also F-linear algebra. No radical decomposition, algebraic splitting-field representation or field-extension dimension has to be output. The semisimple quotient is used only to prove this particular F-linear system is consistent.

A polynomial-size ordinary PC derivation is obtained by first deriving all H (or L,K) lines with degree-3 intermediate matrix products, then deriving the bilinear identity using available lines. The number of variables, source equations and bounded-degree expanded monomials is polynomial in the actual total representation dimension d and arrow/matrix-entry input. Over Q, the required linear systems have polynomial-size coefficients, and Gaussian elimination gives polynomial-bit rational coefficients. This is not a claim about binary-compressed dimensions.

Thus over characteristic zero, both exact source systems in CCC 2023 Open Question 7.3 have ordinary PC degree at most 3 and polynomial expanded proof size for every pair that is nonisomorphic/noncongruent over the algebraic closure. The same large-characteristic scopes of Theorems U and C apply. Matching lower bounds, optimal degree, and arbitrary small characteristic remain separate.

This refinement was independently identified by the independent AI reviewer 1 during peer review, then checked by the independent AI reviewer 2. It uses a standard PC reuse rule, not an added inference rule. Publication priority is unverified; no Lean verification is asserted.

5. Same accounting sharpens the earlier kernel certificate.
In KERNEL-TRANSPORT.md, the lower-left inverse block W is eventually a LINEAR derived polynomial, obtained with degree-3 intermediates. Multiplying this available line by an X entry produces a quadratic line. Therefore the earlier kernel trace proof has PC degree at most 3 (its degree-4 expanded Nullstellensatz certificate remains valid). Both rectangular inverse identities UP=I and PU=I can be available as quadratic lines after this degree-3 preparation. The d-th compound trace argument then has sequential PC degree at most max(3,2d): multiply these already available quadratic lines by determinant cofactors of degree 2d-2, rather than replaying their preparation under every multiplier. This does not assert matching lower bounds or alter the earlier frozen certificate.
