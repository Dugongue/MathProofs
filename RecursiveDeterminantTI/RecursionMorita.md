# Recursive symplectic factorization and relation duality

Over \(F=\mathbb F_3\), repeated extraction of a split symplectic \(M_2(F)\) paired adjoint followed by cropped relation duality reads the determinant character of every original transporter on the recursive domain below. A polynomial-size record gives one ordinary TI instance. Both centroids can be scalar throughout the symmetric top level, with unbounded depth and large relation spaces.

For a transpose type \(s=\pm1\) write \(W^sX=\operatorname{Sym}^2 X\) or \(\Lambda^2 X\), respectively. Start with a based surjection \(B:W^sX\to Z\) of zero common radical and the character \(\det(g)^a\det(h)^b\) on its transporters, \(a,b\in\{0,1\}\).

When the paired adjoint with involution is split symplectic \(M_2(F)\), recover \(X=U\otimes V\), \(U=F^2\), and \(B=\omega\otimes C\) for the standard alternating form \(\omega\) and \(C:W^{-s}V\twoheadrightarrow Z\). Compute the adjoint by linear equations. After the dimension-four test enumerate its 81 elements to find matrix units with the specified involution. Then \(V=e_{11}X\) and \(e_{21}\) identifies the other copy. Each scalar slice in the natural-factor arguments is proportional to \(\omega\), since composing its matrix with the inverse of the matrix of \(\omega\) gives an operator commuting with every matrix unit. This works for both transpose types.

A transporter has \(g=S\otimes T\) and \(hC=\lambda C'W^{-s}(T)\), where \(\lambda=\det S\) is the multiplier of \(\omega\). Its conjugation of the recovered adjoint is inner, and removing this inner map leaves an intertwiner of all matrix units. Set \(r=\dim V\), \(m=\dim Z\), and \(h_0=\lambda^{-1}h\). In product frames,
\[
 \det(g)^a\det(h)^b=\lambda^{ar+bm}\det(h_0)^b.
\]
The factor \((\det T)^{2a}\) is one over \(F\). Keep \(U\times V\to X\), the alternating form with multiplier line, and the product of that line with the normalized output role into the original output. These force the displayed identities and every original transporter extends to them. [Symplectic determinant record](SymplecticDeterminantRecord.md)


## Cropped duality and induction

Let \(R=\ker C\), \(\tau=-s\), and define \(D:W^\tau(V^*)\to R^*\) by the perfect square pairing. Let \(N\) be its common radical and \(Y=V^*/N\). If \(R\ne0\) the cropped product \(D_0:W^\tau Y\to R^*\) is surjective with zero common radical. The inverse dual of \(T\) induces maps \(t_N,t_Y,u\) on \(N,Y,R^*\) via the flags and square action. Keep the linked dual evaluations, inclusions, quotient maps and products.

The determinant of \(W^\tau(T)\) is \((\det T)^{r+\tau}\). Count the contribution of each eigenvalue on diagonal matrices and triangularize over an algebraic closure. The exact sequences for \(R\) and \(N\) give
\[
 \det(g)^a\det(h)^b=\gamma\lambda^{ar+bm}\det(t_N)^c
                  \bigl(\det(t_Y)^c\det(u)^b\bigr),
 \qquad c=(r+\tau)b\bmod2 .
\]
Reciprocal scalars equal themselves in \(F^\times\). For the frame ratio \(\gamma\), take the determinant of the product frame in the raw \(X\) basis, the adapted frame of \(W^\tau V\) given by a basis of \(R\) and lifts of the output basis, and the adapted frame of \(V^*\) given by a basis of \(N\) and lifts of the \(Y\) basis. The target-to-source ratio of the product of these determinants with powers \(a,b,c\) is \(\gamma\). An inverse of a ratio gives the same sign.

If \(c=1\), require \(\dim N\le C_0\log L\) for fixed \(C_0\) and original written length \(L\), and read the exterior top line of \(N\). Recurse on \(D_0\) with weights \((c,b)\). Direct terminals are allowed when each nonzero-weight space is logarithmic. A universal full symmetric or alternating square is a terminal if \(a+(\dim X+s)b\) is even or its input dimension is logarithmic. If \(R=0\) after extraction, the output determinant of \(h_0\) is already the square determinant on \(T\), readable when \(c=0\) or \(V\) is logarithmic. The zero-output-weight branch after extraction uses only the multiplier.

Induct on input dimension. Keep the parent records so every child map is forced by the original transporter and the factor maps. Conversely any original transporter extends to all induced maps. The inductive line reads the parenthesized character. Multiply it by the indicated multiplier and \(N\) contributions and calibrate its frame to read the raw parent character. Mark its generator against the prescribed multiple on the target. Each child has at most half the parent input dimension, and exterior algebras appear only in logarithmic dimension. Label roles and map occurrences by a split coordinate algebra with distinct module multiplicities and tie their copies into fixed direct-sum arrays by order. Compile the polynomial-size diagram once, using the fixed-signature tensor-system reduction to get one ordinary TI instance. Different invariant branch profiles may be rejected by a fixed NO instance. [Role packing](CentroidDeterminantDescentSeed.md) · [Tensor-system compiler](https://arxiv.org/html/2306.03135v2#S4)


## An unbounded family with a genuine determinant constraint

For any depth \(k\ge1\), take \(B_0\) to be the universal square of type \(s_0=(-1)^k\) on an odd-dimensional \(X_0\) of dimension at least three. Choose its rank modulo four so the output dimension \(m_0\) is even. The output determinant of every automorphism is one, since \(\dim X_0+s_0\) is even.

At stage \(i\), set \(V_i=X_{i-1}^*\oplus E_i\), and let \(R_i=\operatorname{im}(B_{i-1}^*)\subset W^{s_{i-1}}X_{i-1}^*\). Take \(C_i\) to be the quotient of \(W^{s_{i-1}}V_i\) by \(R_i\), and put \(B_i=\omega\otimes C_i\), of type \(s_i=-s_{i-1}\). Choose \(\dim E_i\in\{2,4\}\) for an odd-dimensional \(X_{i-1}\) and \(\{3,5\}\) for an even-dimensional \(X_{i-1}\). Then \(r_i=\dim V_i\) can have either odd residue modulo four. The two choices give even and odd square dimensions. Choose even at \(i<k\) and odd at \(i=k\), so \(m_i=\dim W^{s_{i-1}}V_i-m_{i-1}\) is even below the top and odd at the top.

The mixed square between the two summands of \(V_i\) survives freely, as does the full pure square on \(E_i\). The mixed scalar slices alone give zero common radical. Every rank-two mixed slice also forces the duals of both paired adjoints to preserve its support plane, by the balance equation and its transpose. Intersect these planes with a line in one summand fixed and lines of the other summand varying. Each summand has dimension at least two. Thus both duals preserve every line in each summand and act by a scalar there. The mixed slices identify scalars in opposite slots and the nonzero pure \(E_i\) slice identifies them in the same slot. Hence the paired adjoint of \(C_i\) is scalar. Tensoring with the perfect pairing \(\omega\) gives precisely the symplectic \(M_2(F)\) adjoint of \(B_i\), by examining the balance equation entrywise in dual-coordinate bases of the natural factor.

The relation bimap of \(C_i\) evaluates on \(R_i\), so its common radical is exactly \(E_i^*\) since \(B_{i-1}\) has zero common radical. Cropping gives \(B_{i-1}\). The choice of matrix units only changes the product frame and normalized multiplicity maps, as shown by the same factorization of intertwiners used above.

The symmetric top \(B_k\) has scalar centroid. A centroid input map lies in \(M_2(F)\otimes1\), and evaluating it on a pair of multiplicity vectors with nonzero output forces it to be scalar by nondegeneracy of \(\omega\). Its dual relation bimap has full support and scalar paired adjoint. The square of every decomposable \(u\otimes v\) is a relation since \(\omega(u,u)=0\), and each such rank-one slice forces the two dual adjoint maps to preserve its line. Basis tensors and sums sharing a factor then force a common scalar.


Use \((a,b)=(1,1)\) at the top. Its multiplier exponent \(r_k+m_k\) is even. At each step \(c=0\) since \(r_i\) is odd. Each child has weights \((0,1)\) and each lower multiplier has even exponent \(m_i\). Induction from \(B_0\) now gives positive combined sign for every automorphism. Reflecting one raw output-basis vector gives an ordinarily isomorphic target with only negative-sign transporters. The top has even input rank and odd output rank, as required by the cube-zero and exact cubic sign bridges. [Exact cubic orientation](ExactCubicOrientation.md)

The initial rank can grow independently of depth. The first quotient includes at least \(\dim X_0\cdot\dim E_1\) mixed coordinates. At later stages \(m_{i-1}\le (\dim X_{i-1})(\dim X_{i-1}+2)/8\), since \(B_{i-1}\) uses a square on half its input dimension. Subtracting this bound from the square dimension at stage \(i\) gives quadratic growth of \(m_i\) for \(i\ge2\). Thus every residual relation dimension \(m_{i-1}\) can exceed a fixed logarithmic bound by taking the initial rank large relative to the chosen depth. The full top relation space grows quadratically as well. The earlier small-relation test is insufficient for these examples.

The proof covers the stated recursive domain. An input with scalar paired adjoint and large relevant dimensions can fail every branch of this particular recursion. The two scalar centroids alone give no descent guarantee. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
