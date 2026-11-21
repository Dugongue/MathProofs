# Subcubic weighted homomorphism counts and real orthogonal cubic equivalence

For real symmetric matrices \(A\) and finite simple graphs \(X\), write
\[
 Z_A(X)=\sum_{\varphi:V(X)\to[q]}\prod_{ij\in E(X)}A_{\varphi(i),\varphi(j)},\qquad A\in\operatorname{Mat}_q(\mathbb R).
\]
The matrix may be singular, may have diagonal entries, and may have either sign. On rational matrices in the dense binary encoding, testing equality of \(Z_A(X)\) and \(Z_B(X)\) for every simple graph \(X\) of maximum degree three is polynomial-time many-one equivalent to exact real orthogonal equivalence of **one rational homogeneous cubic form**. The reduction to weighted counts from cubic forms outputs positive semidefinite rational matrices. This identifies the weighted-adjacency portion of GP103 with a compact tensor isometry problem. The reductions do not give either a graph-isomorphism upper bound or TOCI-hardness. [Cai–Young, Corollary 39 and the subsequent algorithmic question](https://doi.org/10.4230/LIPIcs.ITCS.2026.32)

## Compressing the counting model

Set \(W_A=\operatorname{im} A\) with its Euclidean inner product and let \(P_A\) be its orthogonal projector. Define the self-adjoint operator \(D_A=A|_{W_A}\), the linear form \(\ell_A(x)=\sum_i x_i\) on \(W_A\), and the cubic \(f_A(x)=\sum_i x_i^3\) on \(W_A\). Equivalently, on the original ambient space the latter two are \(\ell_A(x)=\sum_i(P_A x)_i\) and \(f_A(x)=\sum_i(P_Ax)_i^3\). Testing maximum-degree-three counts is exactly testing the size \(q\) and simultaneous Euclidean equivalence of \((D_A,\ell_A,f_A)\).

To see the forward implication from an isometry, rewrite every count as a contraction on \(W_A\). Each edge inserts the operator \(D_A\), since \(A=P_AAP_A\). The degree-one, degree-two, and degree-three vertices carry \(\ell_A\), the inner-product tensor, and the symmetric trilinear polarization of \(f_A\), respectively. Isolated vertices contribute \(q\). An orthogonal equivalence preserving the operator and the two forms preserves each such contraction.

For the converse, \(K_1\) recovers \(q\). The cycle of length \(j\ge3\) gives \(\operatorname{tr} A^j\). These traces determine all nonzero eigenvalues with multiplicities. Indeed, compare the two finite lists using their union of distinct nonzero eigenvalues. The resulting difference is \(\sum_\lambda c_\lambda\lambda^j\), and the Vandermonde matrix on any consecutive set of sufficiently many exponents \(j\ge3\) is invertible because each \(\lambda\ne0\). In particular both image spaces have the same dimension. If it is zero the claim is immediate.

On the two image spaces both operators are invertible. Choose a common polynomial \(p(t)\) divisible by \(t^3\) and satisfying \(p(D_A)=I\) and \(p(D_B)=I\). Such a polynomial is obtained by inverting \(t^3\) modulo the product of the two characteristic polynomials, whose constant terms are nonzero. Consider a complete orthogonal contraction of copies of \(D_A,\ell_A,f_A\), with the symmetric tensors associated to the forms by polarization. One can suppress each chain of \(D_A\)-vertices to an edge carrying a nonnegative power \(D_A^k\). A component containing only these vertices is a trace already determined by the spectrum. For each remaining edge, replace \(D_A^k\) by \(D_A^k p(D_A)\) and expand. A term \(D_A^j\) with \(j\ge3\) is the contraction along a path of length \(j\) through \(j-1\) degree-two vertices whose local tensors are identities. For loops use a length-\(j\) cycle anchored at the incident vertex. Using fresh internal vertices for each replacement makes each resulting test graph simple even for parallel original edges. Maximum degree does not increase beyond three. The same linear combination applies to \(B\), hence all complete orthogonal contraction values agree. By the real orthogonal Holant converse, there is one real orthogonal equivalence of the three data. The unweighted simple-target version of the image-space criterion is already in Maehara's Lemma 13. The argument here works for general real symmetric edge matrices. [Young's real orthogonal Holant converse](https://doi.org/10.4230/LIPIcs.ICALP.2025.136) · [Maehara, Lemma 13](https://arxiv.org/html/2610.09042#S3.SS1)

## Compile the tuple to one rational cubic

If \(q\) differs, the answer is no and one may output a fixed negative instance. Otherwise work in the full \(\mathbb R^q\). Use \(A\) itself and extend \(\ell_A,f_A\) by first projecting to \(W_A\). Orthogonal equivalence of these extensions reflects equivalence on the image spaces because an operator equivalence preserves the image. Conversely an isometry of the image tuples extends over their Euclidean orthogonal complements. On rational inputs the extensions have polynomial-size rational coefficients. For example choose a rational column basis \(M\) of \(W_A\) and form \(P_A=M(M^TM)^{-1}M^T\). For \(W_A=0\), take \(P_A=0\).

For a tuple \((A,\ell,f)\) in the full Euclidean space, choose a common rational \(L>\max(\|A\|_{\mathrm{op}},\|B\|_{\mathrm{op}})\) for the compared inputs, for instance one more than the largest absolute row sum. Send it to
\[
 \begin{split}
 \Phi_{A,\ell,f}(x,w,z)
 ={}& f(x)-\tfrac12 z^2 \Delta_x f(x)
       +z\,x^T A x +Lzw^2+(z^2-w^2)\ell(x)\\
    &+\left(1-\tfrac13(\operatorname{tr}A+L)\right)z^3 .
 \end{split}
\]
The Euclidean Laplacian of this cubic is \(6z\), so an orthogonal equivalence fixes the \(z\)-axis pointwise. The coefficient of \(z\), restricted to \(z=0\), is the quadratic form \(x^TAx+Lw^2\). The \(L\)-eigenspace is exactly the \(w\)-axis, so the original \(x\)-space is intrinsic. Restriction to \(w=z=0\) recovers \(f\); the \(z\)-linear quadratic recovers \(A\); the coefficient of \(w^2\) at \(z=0\) recovers \(-\ell\). Any tuple isometry extends fixing \(w,z\), since traces and Laplacians respect orthogonal changes. This gives one cubic with polynomial-size rational coefficients.

## Compile one rational cubic to weighted counts

Let \(f\) be a homogeneous rational cubic in \(d\) variables. In polynomial bit time construct rational vectors \(b_i\in\mathbb Q^d\) whose linear and cubic moments are \(0\) and \(6 f\), respectively. First write \(f=\sum_j a_j(\langle v_j,x\rangle)^3\) with polynomially many rational coefficient-vector pairs. For each elementary monomial, ordinary three-variable polarization expresses six times its product as the alternating sum of the cubes of the nonempty subset sums of its three linear factors, including repetitions if the monomial has them. For each pair \((a,v)\), use the four vectors
\[
             (a+1)v,\ (a-1)v,\ -av,\ -av.
\]
Their sum is zero and their cubic moment polynomial is \(6a\langle v,x\rangle^3\).

Let \(M_0=\sum_i b_i b_i^T\). Choose a common rational \(c\) greater than the largest absolute row sum of the two matrices \(M_0\) constructed from the compared cubics. The rational matrix \((cI-M_0)/2\) is positive definite. Factor it as \(RDR^T\) by rational elimination, with \(D\) diagonal and positive. Every positive rational \(s/t\) is an efficiently computable sum of \(O(\log(st))\) rational squares: expand \(st\) in base four, replace a digit \(a\) at position \(j\) by \(a\) copies of the square \((2^j/t)^2\), and add. Thus \((cI-M_0)/2=\sum_j u_j u_j^T\) for a polynomial-size collection of rational vectors. Adjoin \(u_j\) and \(-u_j\) for each \(j\). They cancel in degrees one and three and make the quadratic moment \(cI\). All steps have polynomial bit complexity, using rational elimination with its ordinary determinant size bounds.

Pad the lists for the compared inputs by zero vectors to the same length \(q\), retaining all moments. Let \(B\) be the matrix with those vectors as columns, and form the weighted adjacency matrix \(A=B^TB\). It has rank \(d\) and is rational positive semidefinite. The map \(x\mapsto c^{-1/2}B^Tx\) is an isometry onto \(W_A\), under which the compressed tuple becomes
\[
       (c I,\ 0,\ 6c^{-3/2}f).
\]
Thus equality on all subcubic test graphs holds exactly when the original cubics are orthogonally equivalent. The comparison uses the same nonzero multiplier on both cubic forms. This proves the reverse reduction, with fully rational output matrices and no extraction of algebraic roots in the algorithm. These are paper proofs.
