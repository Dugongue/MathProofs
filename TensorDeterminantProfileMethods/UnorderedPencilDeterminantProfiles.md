# Raw determinant tests from unordered determinant factors

## The exact sufficient theorem

Fix an odd finite field \(F=\mathbb F_q\), a positive integer \(d\), and a constant \(C>0\). Let \(M_A,M_B\) be raw square matrix pencils with label dimension \(\ell\) and matrix side \(n\). The input coordinates in the three modes may be changed independently. Suppose the formal determinant of \(M_A\) is nonzero, every distinct geometric factor has degree at most \(d\), and some \(F\)-rational absolute quadratic factor is represented by a nonsingular symmetric matrix \(B_A\).

Form an operator from each absolute quadratic factor \(Q\), and from the square \(Q=\lambda^2\) of each absolute linear factor \(\lambda\). Use independent nonzero representatives for all lines. Interpret \(Q\) as a symmetric matrix in the odd characteristic. Let \(e\) be the degree of its field of definition as a factor line, and put
\[
 L_Q=B_A^{-1}Q.
\]
Partition the factors by original degree, exact multiplicity, and field-of-definition degree \(e\). The factor \(B_A\) can either remain in its class or be removed consistently. For each class \(c\) and each \(1\le j\le\ell^2\), form the sum
\[
 S_{c,j}=\sum_{Q\in c} L_Q^{\,j(q^e-1)}.
\]
The sum is over the whole class of geometric factors, including all Frobenius conjugates. Let \(\mathcal C_B\) be the simultaneous commutant of these operators on the \(F\)-label space.

If for one choice of \(B_A\) we have \(\dim_F\mathcal C_B\le C\log_q L\), where \(L\ge2\) is the input length, then a deterministic polynomial-time algorithm computes the full set of determinant triples of transporters. In particular it yields a polynomial-time one-instance reduction of SL-TI to ordinary TI on this raw class. In fact no TI oracle calls are needed. The number and multiplicities of geometric factors, the common splitting degree, and matrix-mode adjoint dimensions are unrestricted.

## 1. Compute and compare the aggregates

Use separate finite-field low-degree factor recovery from the earlier MathProofs determinant-descent proof. It uses determinant evaluations and a polynomial-size bounded-degree curve to find a line with disjoint simple roots of the reduced absolute factors. It recovers bounded-degree factors by truncated coprime Hensel lifting and tests every candidate by bounded-degree resultants. Every selected factor is obtained in a separate extension of degree at most \(n\) over \(F\), by its Frobenius orbit. This subroutine and its fixed-characteristic field-construction details are in the [geometric factor recovery appendix](GeometricPencilFactorRecovery.md). Its algebraic interfaces are ordinary univariate factoring and Hensel lifting, rather than a full expansion of the determinant polynomial. [Shoup, fixed-characteristic irreducible polynomial construction](https://www.shoup.net/papers/detirred.pdf)

On the source try each of the at most \(n\) possible rational \(B_A\). In each class the sums are independent of the chosen normalized representatives, because multiplying one geometric form \(Q\) by any scalar of its field leaves \(L_Q^{j(q^e-1)}\) unchanged. This also applies when \(Q\) is the square of a representative of a linear factor. Frobenius of \(F\) permutes the summands and fixes \(B_A\), so each separate Frobenius-orbit sum is an \(F\)-matrix. Compute this sum in that orbit's own coefficient field, then descend its entries. Exponentiation uses \(O(e\log q+\log j)\) matrix multiplications by binary powering. Thus no exponential-cardinality field enumeration or common compositum is required.

A genuine transporter satisfies \(M_B(fx)=hM_A(x)g^{-1}\), and multiplying determinants gives \(P_B(fx)=(\det h/\det g)P_A(x)\). Hence it sends the absolute factor lines to corresponding factor lines of the same degrees, multiplicities and fields of definition. If \(B_B\) is the mate of \(B_A\), their relation and that of a corresponding \(Q_B,Q_A\) are
\[
 f^{\mathsf T}B_B f=\lambda_0 B_A,\qquad
 f^{\mathsf T}Q_B f=\lambda_Q Q_A,
\]
where \(\lambda_0\in F^\times\) and \(\lambda_Q\in\mathbb F_{q^e}^\times\). This gives
\[
 (B_B^{-1}Q_B)f=(\lambda_Q/\lambda_0)f(B_A^{-1}Q_A).
\]
Taking the prescribed powers removes the multiplier and summing over each class removes the permutation. The target aggregate therefore obeys \(S'_{c,j} f=fS_{c,j}\) for every \(c,j\).

For one successful source choice, enumerate every possible target mate of \(B_A\) and solve all these simultaneous intertwiner equations by linear algebra over \(F\). If there is one invertible solution \(f_0\), the entire solution space is the left translate \(f_0\mathcal C_B\). Indeed \(f_0^{-1}f\) commutes with each source operator exactly when \(f\) satisfies the equations. Discard a branch of dimension larger than \(C\log_q L\) and enumerate all maps in the others. There are at most \(L^C\) maps in each. Retain the invertible maps and test their actual matrix-mode transport equations. It is unnecessary to match any of the individual nonreference factors. If a target violates the degree promise, it has no true transporter. Processing it with the same bounded recovery algorithm may yield extra candidates, which cannot pass the literal matrix-mode test.

## 2. Test and read the literal determinant triple

For each retained \(f\), test ordered module isomorphism between the tuples of all slices \(M_A(u_i)\) and \(M_B(fu_i)\). On \(X\oplus Y\), use the two vertex projections and the slice arrows, each extended by zero on \(Y\). An isomorphism is precisely a block-diagonal pair \((g,h)\) obeying the tensor equations, so constructive module isomorphism supplies the reference pair whenever one exists. [Brooksbank–Luks, Testing Isomorphism of Modules](https://ix.cs.uoregon.edu/~luks/ModIso.pdf)

Let \(D\) be the end algebra of the ordered source slices. All matrix pairs for the fixed label map are the found reference multiplied by \(D^\times\). Compute \(J=\operatorname{Rad}D\) and its explicit Wedderburn quotient. For a factor \(\operatorname{Mat}_{s_i}(E_i)\) of \(D/J\), its action on each radical grade \(J^aV/J^{a+1}V\), \(V=X,Y\), is a direct sum of natural simple modules. Its total multiplicity \(m_{V,i}\) is read from the dimensions of the corresponding central-idempotent images, divided by \(s_i[E_i:F]\). The determinant product over the filtration gives the possible pairs
\[
 \left(\prod_i a_i^{m_{X,i}},\ \prod_i a_i^{m_{Y,i}}\right),
 \qquad a_i\in F^\times .
\]
The norm of a determinant over \(E_i\) can be any \(a_i\) by surjectivity of finite-field norms, and the different quotient units lift independently because \(J\) is nilpotent. The subgroup product has at most \((q-1)^2\) elements. Multiply by the two reference determinants and append \(\det f\), then take the union over verified \(f\). This is the exact determinant profile, and determinant one is unaffected by converting dualized modes back to the usual tensor convention. [Ivanyos–Qiao, Theorem 18](https://arxiv.org/html/1708.03495#S3.SS5.SSS1)

## 3. A growing example requiring the unordered aggregate

Work over \(\mathbb F_3\). Choose \(\ell=12a+1\) with \(a\ge1\) and \(r=(\ell-1)/2\). Let \(Q_0=\sum_{i=1}^{\ell}x_i^2\). Use path-edge linear factors \(\lambda_i=x_i+x_{i+1}\) of multiplicity one, and the factor \(x_1\) of multiplicity two. The additional linear factor \(t=x_\ell\) will have multiplicity \(r-1>2\). These are all distinct lines. The class of path factors gives, at \(j=1\),
\[
 S_1=-\sum_{i=1}^{\ell-1}(e_i+e_{i+1})(e_i+e_{i+1})^{\mathsf T}.
\]
The class of multiplicity two gives \(S_2=E_{11}\). The first is symmetric tridiagonal with every subdiagonal entry nonzero, so \(e_1,S_1e_1,\ldots,S_1^{\ell-1}e_1\) form a basis by progressive support and nonzero leading entries. Symmetry gives the analogous row basis. Thus \(S_1^iE_{11}S_1^j\) span the full matrix algebra, and the simultaneous commutant is scalar.

No tuple of a constant number \(k\) of these factors can give the earlier small-commutant criterion by matching only individual quadratic forms or squared linear forms. Every form besides \(Q_0\) has rank one. Given at most \(k\) such rank-one marks, let \(U_0\) be the intersection of their kernels and \(U_1\) the span of the images of their relative operators with respect to \(Q_0\). All operators with image in \(U_0\) and vanishing on \(U_1\) commute with the selected rank-one relative operators. Their dimension is at least \((\ell-k)^2\). They still commute if one uses any other nonsingular combination from the tuple as reference, since this replaces the operators by multiplication with the inverse of a linear combination commuting with the same operators. This explains exactly where taking the full unordered family changes the bound.

To realize these factors as a tensor determinant, use a Witt basis on the first \(2r\) coordinates. The dot form of even dimension \(2r\) is split over \(\mathbb F_3\) when \(r\) is even, as its discriminant has the hyperbolic square class; here \(r=6a\). In these coordinates write \(Q_0=t^2+\sum_{j=1}^r u_jv_j\). Take the arrowhead block
\[
 A(x)=\begin{pmatrix}t&u^{\mathsf T}\\-v&tI_r\end{pmatrix},
 \qquad \det A=t^{r-1}Q_0 .
\]
Add one scalar block for each \(\lambda_i\) and two scalar blocks for \(x_1\). If \(x_1=\cdots=x_\ell=1\), then \(Q_0=\ell=1\) over \(F\) and all the scalar blocks and \(t\) are nonzero. Thus the block-diagonal pencil has an invertible reference slice \(x_0\). The absolute quadratic \(Q_0\) has rank \(\ell\ge3\) so it is irreducible over the algebraic closure.

Join successive diagonal blocks by upper-superdiagonal linear blocks vanishing at \(x_0\), each chosen to make its two-level extension nonsplit after left normalization by the inverse slice at \(x_0\). These choices are possible by linear algebra: for adjacent sizes \(d_1,d_2\), the split blocks have the form \(H N_2(x)-N_1(x)H\), dimension at most \(d_1d_2\), whereas the space of admissible blocks has dimension \((\ell-1)d_1d_2\). The first normalized diagonal module is absolutely simple. Let \(L=A(x_0)^{-1}\) and use indices \(0,\ldots,r\). The operators include \(Le_0 e_j^{\mathsf T}\) and \(Le_j e_0^{\mathsf T}\) for each tail \(j\), because the \(u_j,v_j,t\) are independent. A nonzero invariant subspace with a nonzero tail coordinate contains \(Le_0\). If it contains a vector with only head nonzero, it contains all independent \(Le_j\) for the tails, so some vector has a nonzero tail. The head entry of \(Le_0\) is nonzero by the inverse cofactor formula. Hence the subspace contains every \(Le_j\), proving simplicity over the closure.

The other diagonal modules are one-dimensional and simple. The nonsplit adjacent extensions ensure the only invariant subspaces are the displayed prefixes. This follows by induction: a submodule of a prefix projecting onto its last factor would split the last two-level extension if its intersection with the previous prefix lay in the prefix two levels earlier. Thus it contains the previous prefix and equals the entire prefix. The first simple factor occurs only once, so a nonzero endomorphism cannot have nonzero kernel: its nonzero image contains that first simple, whereas a quotient by a nonzero prefix lacks it. Restriction of an endomorphism to the first block is scalar by absolute simplicity. Subtracting this scalar leaves an endomorphism with nonzero kernel, so leaves zero. The ordered matrix-mode adjoint is scalar.

The off-diagonal blocks do not change the determinant factorization. Every tensor stabilizer has scalar label map, because it preserves the aggregate operators from the unique quadratic reference and the listed multiplicities. Its two matrix maps are then scalar by the ordered adjoint computation. The other two pair adjoints are scalar as well. An invertible element of a left or right idealizer of the concise slice space would induce a stabilizer fixing the other matrix mode pointwise, so every such unit is scalar. Over \(\mathbb F_3\) a finite-dimensional unital algebra with just the two scalar units is \(\mathbb F_3\). A nonzero radical gives additional units \(1+j\), and a nontrivial matrix block, larger field or multiple simple components of the semisimple quotient also gives more than two units. Thus these raw pencils have scalar full stabilizer and all three scalar pair adjoints. Their side is \(\ell+r+2\), which is odd and differs from the label dimension.

## Literature and exact scope

Chen, Grochow, Qiao, Tang and Zhang's Part III mentions special-linear actions in its subgroup discussion. Its Open Question 1.8 explicitly lists orthogonal, unitary and symplectic actions. Question 1.9 asks about special-linear containment and equality. [Part III arXiv:2306.03135v2](https://arxiv.org/html/2306.03135v2)

Grochow and Qiao's Part IV obtains polynomial search- and counting-to-decision for class-two exponent-\(p\) groups in the Cayley-table model. Its stated tensor-scale search still has \(q^{O(n+m+\ell)}\) overhead. Polynomial time in the order of an explicitly given group is exponential in the corresponding tensor dimensions. [Part IV arXiv:2306.16317, Section 7.3](https://arxiv.org/html/2306.16317#S7.SS3)

The recent linear-code search-to-decision result of Biasse, Micheli, Prada and Waitkevich uses polynomially many adaptive calls on monomial equivalence, where a coordinate has a polynomial number of images. The paper does not give a polynomial list for the image of an arbitrary vector under a full linear tensor map. The analogous observation here is that orbit aggregates remove unknown factor permutations and scales without attempting to match them individually. [Code-equivalence preprint arXiv:2609.31517](https://arxiv.org/abs/2609.31517)

Grochow, Qiao, Stange and Sun's Part V studies ordinary TI over commutative rings. Its arithmetic orientation statements for Bhargava cubes are dimension-specific and do not supply arbitrary dimensional special-linear restrictions. The recent average-case result of Li, Li, Qiao, Tao and Wang gives polynomial algorithms on quantified fractions of random algebra/matrix-code/order-four tensor inputs; it does not prove worst-case coverage of the scalar-stabilizer class. [Part V arXiv:2611.00735](https://arxiv.org/html/2611.00735v1), [Average-case TI arXiv:2604.00591](https://arxiv.org/abs/2604.00591)

Targeted Hexagon searches surfaced nearby formalized matrix multiplication rank and computational representation results but no general determinant-constrained TI algorithm. The research above remains informal and scoped to the displayed structural hypothesis; universal raw scalar-stabilizer coverage and a universal SL-TI reduction remain unresolved here. Publication priority is unverified.
