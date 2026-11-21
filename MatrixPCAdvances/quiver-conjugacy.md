# Exact conjugacy degree from multiplicities

Take two geometrically nonisomorphic representations of a labelled quiver with a common dimension vector over a field of characteristic \(p>0\). Use forward linear intertwiner equations and both quadratic inverse equations at every vertex. Compute the indecomposable multiplicities \(a_W,b_W\) over an algebraic closure. For a differing type \(W\), set
\[
e_W=
\begin{cases}
2,&\min(a_W,b_W)=0,\\
\min\bigl(2p^{v_p(|a_W-b_W|)},\min(a_W,b_W)+2\bigr),&\min(a_W,b_W)>0 .
\end{cases}
\qquad e_*=\min_{W:a_W\ne b_W}e_W .
\]
The degree \(D\) satisfies \(e_*\le D\le\max(3,e_*)\). In particular it is exactly \(e_*\) if \(e_*\ge3\). When \(e_*=2\), the degree is exactly 2 if the constant 1 lies in the span of the inverse defects after parametrizing the forward intertwiners, and 3 otherwise. The formula holds with field equations over \(\mathbb F_Q\), \(Q>2\).

For the upper bound, derive reverse intertwining at degree 3 and project the forward and reverse variables onto their respective intertwiner spaces. The projected inverse identities are consequences in degree at most 3. Read the opposite corners of the quotient of the endomorphism algebra of the direct sum by its radical. On each geometric indecomposable type, the corner maps are rectangular matrices on the multiplicity spaces. The quotient is linear and preserves these products. A type missing on one side gives a constant inverse defect in degree 3. Otherwise substitute the two opposite corner matrices into an exact rectangular refutation. Linear substitution preserves degree after the premises have been derived. Descent through scalar extension follows by fixed-degree subspace closure. [Prior multiplicity and projection argument](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/AlgebraicComplexity.md)

For the lower bound when every differing type occurs on both sides, use common bases on each repeated indecomposable. Substitute \(U_W\otimes I_{W_v}\) and \(V_W\otimes I_{W_v}\) at each vertex \(v\) with opposite rectangular shapes and independent variables. Use the identity on equal types and zero across distinct types. Every arrow line vanishes and both inverse families become repeated entries of disjoint rectangular inverse systems. The degree of their disjoint union is the minimum of the individual degrees. This uses the tensor product of the bounded-degree quotient spaces of the disjoint systems, equipped with the total-degree filtration. Multiplication on degree less than the cap agrees with multiplication on the appropriate component of this filtration. The image of 1 is the tensor of nonzero images of 1 if each component fails to refute at that cap. With a missing type it suffices to observe that the only source lines below degree 2 are homogeneous linear equations. [Disjoint-system lemma](https://github.com/Dugongue/MathProofs/blob/main/PortfolioIsomorphismCrossovers/AlgebraicComplexity.md#2-degree-bounds-for-disjoint-axiom-families) · [Exact rectangle theorem](rectangular-inverses.md)

For the finite-field lower bound use the decompositions and linear changes of basis over the input field. Finite division rings are fields, and each residual matrix factor splits into factors with exactly the same two multiplicities after scalar extension. This follows by extending the nilpotent radical and observing that the extended quotient is semisimple by separability. With the base-field substitutions, each original field equation maps to a linear combination of field equations of the rectangular variables, or zero. For the degree-two test, the field equations with \(Q>2\) are above the cap. A homogeneous linear parametrization kills the forward equations. The remaining axioms are quadratic plus constant. Unless their span contains 1, every nonzero member of the span has degree 2, which rules out any multiplication in a degree-two proof. In the other direction, the difference between a polynomial of degree at most 2 and its linear parametrization is derivable from the forward linear equations in degree at most 2, by expansion and replacement.

## Worst case for a single matrix

For \(N\ge4\), the exact worst-case degree for \(N\times N\) matrix conjugacy is
\[
C_p(N)=\max\left(3,\ \max_{\substack{q=p^j,\ j\ge0\\q\le N-2}}\min\left(2q,\left\lfloor\frac{N-q}{2}\right\rfloor+2\right)\right).
\]
The claim holds over any field of characteristic \(p\) for geometric nonconjugacy. For one matrix, field and geometric similarity coincide by rational canonical form. It also holds over \(\mathbb F_Q\), \(Q>2\), with the field equations.

For the upper bound, take the least \(q=p^{v_p(|a_W-b_W|)}\) among the differing Jordan types. Reading that type bounds degree by \(\max(3,2q)\). There are types with differences of both signs, since the dimension sums agree. Every difference is a multiple of \(q\). If the smaller multiplicities of one positive and one negative type are \(s,t\), one matrix has dimension at least \(s+t+q\). The smaller of \(s,t\) is at most \(\lfloor(N-q)/2\rfloor\). Reading that type gives the other bound by descending minors, or degree 3 when its smaller multiplicity is zero. If \(q>N-2\), the dimension bound forces a missing type, hence degree at most 3.

For every admissible \(q\) take \(b=\lfloor(N-q)/2\rfloor\), \(a=b+q\), and the idempotents \(\operatorname{diag}(I_a,0_b)\) and \(\operatorname{diag}(I_b,0_a)\), padded on both sides with an equal zero block. Their refutations require at least the corresponding rectangular degree by substituting the opposite rectangle variables on the two eigenspace blocks and an identity on the padding. The degree-3 floor comes from the fixed \(4\times4\) Jordan-block pair in the earlier work. For \(Q>2\) its degree-2 obstruction also applies because those field equations have degree above 2. [Degree-three Jordan example](https://github.com/Dugongue/MathProofs/blob/main/MatrixIsomorphismPC/CONJUGACY-SHARPNESS.md)

In the three smaller positive dimensions the worst case is 2. If the two minimal polynomials differ, some polynomial \(f\) annihilates one matrix and does not annihilate the other. The forward arrow equations linearly imply \(Xf(A)=f(B)X\). Multiplying the appropriate vanishing product by \(Y\) and using the inverse equations gives a nonzero constant in degree 2. If the minimal polynomials agree, over the algebraic closure the eigenvalues and largest Jordan block size at each eigenvalue are fixed. In dimension at most three the only nonconjugate possibility is two semisimple eigenvalues with multiplicities \(2,1\) interchanged. The forward equations force \(X\) to respect these eigenspaces, so the diagonal parts of \(XY\) and \(YX\) expose both rectangular products in degree 2 without reverse intertwining. Their size gap is 1. Scalar pairs with distinct scalars supply degree-2 examples in all three dimensions.

For every \(p\)-power \(q\ge2\), this gives \(C_p(N)=2q\) on \(5q-4\le N\le(p+4)q-3\). Indeed \(q\) is saturated while the \(pq\) term is at most \(2q\), and all larger powers contribute at most as much as \(pq\). In the range \(5q\le N<5pq\), the exact formula gives \(C_p(N)=\max(2q,(N-pq)/2)+O(1)\), with the same reading even if \(pq>N\). The two contributions cross at \(N=(p+4)q\). The ratio \(C_p(N)/N\) decreases on the first portion and increases on the second up to bounded rounding errors divided by \(N\). Thus
\[
\liminf_{N\to\infty}\frac{C_p(N)}N=\frac2{p+4},
\qquad
\limsup_{N\to\infty}\frac{C_p(N)}N=\frac25 .
\]
In characteristic zero the same quotient readout gives degree at most 3 on all geometrically nonisomorphic quiver representations, since every unequal pair of sizes is separated by rectangular trace. The degree-two span test applies verbatim. For single matrices this gives worst-case degree exactly 3 in dimensions at least four by the earlier degree-three family, and exactly 2 in the smaller positive dimensions by the preceding argument.

This gives the exact degree profile for the conjugacy system in [GGPS Open Question 7.3](https://arxiv.org/html/2305.19320#S7.SS3).
