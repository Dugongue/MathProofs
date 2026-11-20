# A raw finite-field determinant-sum test for the third constraint

Work with an explicit three-tensor over \(F=\mathbb F_3\), written as a square matrix pencil \(M_X(z)=\sum_{i=1}^r z_i M_{X,i}\) of size \(n\) on the two matrix modes. The third mode acts by an invertible change of the argument \(z\). The signed comparisons use source and target coordinate frames. This is an informal deterministic reduction on a stated domain.

## The invariant and the exact verdict

Define
\[
I(M)=\sum_{z\in F^r}\det M(z)\quad\text{in }F.
\]
For any actual transporter \(M_S(Cz)=P M_T(z)Q^{\mathsf T}\), changing the summation variable by the bijection \(C\) gives
\[
I(M_S)=\det P\det Q\,I(M_T).
\]
If the two sums are nonzero and equal, retain the first and third signs in one two-sign TI instance on the original pair. The product identity then forces the second sign on the same witness. If the sums have ratio \(-1\), the original three-sign answer is NO. A zero versus nonzero mismatch excludes even ordinary equivalence. The statement covers all inputs for which a nonzero sum is computed at both endpoints.

We give a polynomial evaluation algorithm whenever both endpoint pencils have known label bases of small total slice-rank excess. These can be their raw bases or bases obtained by the recovery below. The verdict is independent of the label basis and is valid even if the two computations use unrelated label bases.

## Evaluate the sum at small total slice-rank excess

For a chosen label basis, put \(d_i=\operatorname{rank}M_i\) and \(D=\sum_i d_i\). Choose rank factorizations \(M_i=L_iR_i\). Write \(L=[L_1\ \cdots\ L_r]\), and stack the \(R_i\) as \(R\). The pencil is \(L\operatorname{diag}(z_i I_{d_i})R\). If either \(L\) or \(R\) has rank less than \(n\), the answer is zero. Otherwise \(D\ge n\), and set \(k=D-n\). Assume \(k=O(\log(2+\ell))\) for explicit input length \(\ell\).

Let \(B_i\) be the index block of size \(d_i\) in the stacked coordinates. By Cauchy–Binet, for subsets \(A\subseteq[D]\) of size \(n\), the determinant is the sum of terms
\[
 \det L_{[:,A]}\det R_{[A,:]}\prod_i z_i^{|A\cap B_i|}.
\]
The field sum of a power \(z^a\) is zero when \(a=0\) or \(a\) is odd, and is \(-1\) when \(a>0\) is even. Hence the surviving subsets have a positive even number of selected indices in every block, all with the same multiplier \((-1)^r\).

Let \(K\) be the \(D\times k\) matrix of a basis of \(\ker L\), and \(N\) the \(k\times D\) matrix whose rows are a basis of the annihilator of \(\operatorname{im}R\). The complementary-minor identities are
\[
\det L_{[:,A]}=c_L\epsilon(A)\det K_{[A^{\complement},:]},\qquad
\det R_{[A,:]}=c_R\epsilon(A)\det N_{[:,A^{\complement}]} .
\]
Here \(\epsilon(A)\) is the sign of putting \(A\), then its complement, in coordinate order. For the first formula the top wedge of the rows of \(L\) is proportional to contraction of the ambient volume by the top wedge of \(\ker L\). Both are nonzero \(n\)-covectors on \(F^D/\ker L\). The second formula is the dual argument. Evaluate each formula at any pivot minor of the corresponding full-rank matrix to compute its nonzero constant. Multiplying cancels both permutation signs.

Use the algebra \(\Lambda F^k\otimes\Lambda F^k\) with multiplication \((a\otimes b)(c\otimes d)=(a\wedge c)\otimes(b\wedge d)\). An index \(j\) contributes \(x_j=K_{[j,:]}\otimes N_{[:,j]}\) in bidegree \((1,1)\). In block \(B_i\), expand \(\prod_{j\in B_i}(1+x_j)\) by processing indices in order. Retain only bidegrees \((b_i,b_i)\) for which \(d_i-b_i\) is positive and even. Multiply the retained block elements in block order and read the top-top coefficient. Its terms are exactly the products of the two complementary minors for the surviving subsets. Multiplying by \(c_Lc_R(-1)^r\) gives the requested sum.

Each state has dimension \(4^k\), so even direct multiplication in its exterior-monomial basis is polynomial in \(\ell\) at the stated excess bound. Empty or ineligible blocks give zero according to the same even-positive rule. A rank-deficient factorization and \(D<n\) have already been handled. The algorithm never enumerates the label vectors.

## An unbounded nonsplit scalar-centroid family

For any \(t\ge2\), put \(n=4+2t\) and take labels \(x,y,z_1,\ldots,z_t\). Let \(J\) consist of two copies of the \(2\times2\) matrix sending the first coordinate vector to the second and the second to minus the first. Thus \(J^2=-I_4\). Choose \(E=e_1v^{\mathsf T}\) where the restriction of \(v^{\mathsf T}\) to every bottom two-space is nonzero. Use the pencil
\[
M(x,y,z)=
\begin{pmatrix}
xI_4+yJ&xE\\
0&\bigoplus_i z_iI_2
\end{pmatrix}.
\]
The coordinate slice ranks are \(4,4,2,\ldots,2\), giving \(D-n=4\). The determinant is \((x^2+y^2)^2\prod_i z_i^2\), which is nonsplit over \(F\). The squared norm on \(F^2\) is one on its eight nonzero points and zero at the origin, so \(I(M)=(-1)^{t+1}\ne0\). All three mode dimensions grow. The pencil is concise, since its slices are independent and their image and transpose-image spans both have dimension \(n\). Reflecting just one matrix mode produces an ordinarily equivalent pair with negative three-sign verdict.

To verify scalar centroid, write its equations as \(PM(z)=M(z)Q=M(Cz)\), using the transpose convention for the right mode. The \(y\)-slice and all \(z_i\)-slices in \(PM=M Q\) force \(P,Q\) to be block diagonal with equal paired bottom blocks. Comparison to \(M(Cz_i)\) makes those blocks \(\lambda_iI_2\). The top-left block in comparison to \(M(Cy)\) must be \(P_0J=aI+bJ\), with \(a=0\) since the \(xE\) block vanishes in \(P M_y\) and \(E\ne0\). Thus \(P_0=bI\), and the \(x\)-comparison gives \(Q_0=bI\) and \(bE=E\bigoplus_i\lambda_iI_2\). Every bottom block of \(E\) is nonzero, so all \(\lambda_i=b\). Slice independence then makes the third action scalar.

## Recover a small-excess basis after arbitrary rebasing

Compute the span \(J_3\) of the cubic polynomials given by all \(3\times3\) minors of the pencil. Its construction takes polynomial time, and exterior powers of the invertible left and right maps establish covariance. In the example, \(J_3\) contains every cubic monomial except \(z_i^3\). Bottom minors supply the mixed bottom monomials. Triangular minors with one or two core rows supply the mixed core and bottom monomials, since core entries span \(x,y\) and core \(2\times2\) minors span \(x^2,xy,y^2\). The core adjugate gives \(x(x^2+y^2)\) and \(y(x^2+y^2)\). Taking rows \(1,2,3\), a bottom column with nonzero \(E\)-entry and core columns \(2,3\) or \(1,3\) yields a nonzero scalar times \(x^3\) or \(x^2y\), respectively. These polynomials span the whole binary cubic space. No minor contains \(z_i^3\), since the corresponding single slice has rank two.

Intersect \(J_3\) with the subspace of cubes of linear forms, and take cube roots in that subspace. This is linear in characteristic three and yields the plane spanned by \(x,y\) in the label dual. Let \(U\) be its annihilator in the label space. Compute the space
\[
Q_2=\{f\in\operatorname{Sym}^2 U^*:f\cdot U^*\subseteq J_3|_U\}.
\]
It is the span of the cross products \(z_i z_j\), \(i\ne j\), since the coefficient of each missing \(z_i^3\) in \(z_if\) reads the diagonal coefficient of \(f\). Its annihilator in symmetric matrices on \(U\), under canonical tensor contraction, is precisely the space of diagonal matrices in the example's basis. Denote it by \(\mathcal S\). Solve \(A H=H A^{\mathsf T}\) for all \(H\in\mathcal S\). Solving on each of the diagonal rank-one spanning matrices shows the resulting space is the split diagonal algebra of endomorphisms of \(U\). Compute its one-dimensional joint eigenspaces by splitting successively into the kernels of \(A-\lambda I\) for each basis element \(A\) and \(\lambda\in F\). These are the rank-two label axes. No enumeration of bases is needed.

Finally let \(K_0\) be the common kernel of the slices from \(U\). Let \(C_0\) be the span of all \(M(z)K_0\), computed using a raw label basis. They are the pure core input and output in the example. The space of label vectors whose slices have image in \(C_0\) is the complementary core label plane. Its nonzero slices all have rank four, as \(x^2+y^2\ne0\) on nonzero \(F\)-points. Taking a basis of that plane and one vector on each recovered axis gives the required small-excess basis after arbitrary rebasing in all three modes. Each recovery step uses linear algebra. On other inputs one may check that the resulting vectors give a valid basis and verify the rank budget before using the sum algorithm. Passing both endpoint rank and nonzero checks is sufficient for validity.

## Relation to earlier work

The relative scalar here is a finite-field sum rather than a coefficient extracted from a split determinant. The new evaluation uses exact exterior states on the complement of the raw rank factorization. Each local verification checks the actual selected complement, following the design principle of the pinned AgentAlphaXiv exact-verifier study. The cubic-minor span technique reuses the earlier raw recovery in the project. The result supplies a one-instance answer on the stated class and leaves arbitrary raw pairs open. [AgentAlphaXiv study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf) · [Earlier cube-minor recovery](https://github.com/Dugongue/MathProofs/blob/main/TensorProjectionSelectors/TwinTerms.md) · [Earlier split factor method](https://github.com/Dugongue/MathProofs/blob/main/RawTensorSignReductions/Multisymmetrizer.md)