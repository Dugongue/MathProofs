# Quartic sparse proof exponent upper bound on the degree-two conjugacy stratum

Let \(A,B\) be matrices of side \(n\) over any field. Use ordinary Polynomial Calculus (PC) on the original entries of \(H=XA-BX\), \(XY-I\), and \(YX-I\), with binary linear combinations and multiplication by one variable. Size counts every monomial occurrence on used lines. **Every instance admitting a degree-two refutation has a degree-two refutation of size \(O(n^4\log^2(2n))\).** When the minimal polynomials differ the size is \(O(n^4\log(2n))\). These bounds allow arbitrary input bases and arbitrary finite or infinite coefficient fields. [Published equations](https://arxiv.org/html/2305.19320#S7.SS3)

## Fast powers in degree one

Write \(H_j=XA^j-B^jX\). Each individual entry of \(H_j\) has at most \(2n\) terms in the original variables, independently of \(j\). For nonnegative integers \(r,s\),
\[
 H_{r+s}=H_r A^s+B^r H_s.
\]
Given the entries of \(H_r,H_s\), each entry of the right-hand matrix follows by a balanced binary sum of at most \(2n\) scalar-weighted lines. The sum of support sizes at any level is at most the total leaf support \(4n^2\). The cost for all entries is therefore \(O(n^4\log(2n))\) and every step uses degree one. The actual output has a second cancellation, because the displayed identity puts it back in the form of a Sylvester equation with support at most \(2n\). Thus we may iterate without multiplying the support cost at successive steps. Computing the needed constant matrix powers has no effect on sparse proof size.

Use the addition chain given by binary powering. For any \(k\ge1\), all \(H_k\) entries have degree-one derivations of size \(O(n^4\log(2n)\log(2k))\). There are no extra \(X\) variables.

## Short refutations via trace or an annihilated vector

Suppose some split eigenvalue has differing algebraic multiplicities in the coefficient field. In a splitting field let \(\lambda_1,\ldots,\lambda_\ell\) be the distinct eigenvalues across both inputs and \(d_i\) the signed algebraic multiplicity differences, viewed in that field. The vector \(d\) is nonzero. The Vandermonde matrix \((\lambda_i^k)_{0\le k<\ell,\ 1\le i\le\ell}\) is invertible in every characteristic, so some \(\sum_i d_i\lambda_i^k\) is nonzero. The term at \(k=0\) is zero because the sides agree. Since \(\ell\le2n\), there is a power \(1\le k<2n\) with
\[
 \operatorname{tr}(A^k)-\operatorname{tr}(B^k)
 =\sum_i d_i\lambda_i^k\ne0 .
\]
The ordered powers and traces and the nonzero constant are in the original field. The splitting-field calculation only proves existence of a choice of \(k\). One can find \(k\) by computing the first \(2n-1\) traces in the input field.

From \(H_k\) and the inverse equations derive the scalar by
\[
 \operatorname{tr}(A^k)-\operatorname{tr}(B^k)
 =\operatorname{tr}(A^k(I-YX))-\operatorname{tr}(B^k(I-XY))
   +\operatorname{tr}(YH_k).
\]
This final combination has \(O(n^2)\) input or single-variable-multiplied lines of support \(O(n)\). Its balanced addition costs \(O(n^3\log(2n))\), and scaling by the inverse constant yields one. Combined with the power lemma it gives the asserted degree-two bound.

If the minimal polynomials differ, one of those polynomials annihilates exactly its named matrix. For example, take \(f(B)=0\) and some standard vector \(v\) with \(u=f(A)v\ne0\). The telescoping identity for \(Xf(A)-f(B)X\) puts each entry of \(Xu\) in the linear span of \(H\). Derive each of the \(n\) needed lines directly as a balanced linear combination of at most \(n^2\) raw entries of \(H\), each of support at most \(2n\). This costs \(O(n^4\log(2n))\). Multiply the lines by the entries of a single row of \(Y\), add, and compare to the same row of \((YX-I)u\), where that row is chosen to have nonzero \(u_i\). The additional cost is \(O(n^2\log(2n))\). If \(f(A)=0\) and \(f(B)\ne0\), use a nonzero row of \(f(B)\) and \(XY-I\). The established exact degree-two test says these two cases cover the whole degree-two stratum. [Degree-two classification](ConjugacyDegree.md)

## Extension to polynomials and simultaneous commuting tuples

Define \(D_f=Xf(A)-f(B)X\). For every polynomial \(f\) its entries admit homogeneous linear derivations of size \(O(n^{9/2}\log(2n))\). Reduce \(f\) modulo the least common multiple of the minimal polynomials, of degree at most \(2n\). With \(b=\lceil\sqrt{2n}\rceil\), divide its coefficient list into \(O(b)\) contiguous groups and write \(f(t)=\sum_i t^{bi}f_i(t)\) with \(\deg f_i<b\). Precompute \(D_{t^j}\) for \(j\le b\) using \(D_{uv}=D_u v(A)+u(B)D_v\). Build the \(D_{f_i}\) by linear combinations, and combine those blocks by Horner evaluation at \(t^b\), again using the product identity. All outputs \(D_u\) have support at most \(2n\) per entry. Precomputation and Horner evaluation use \(O(b)\) steps of size \(O(n^4\log(2n))\). Direct scalar combinations for the short coefficient blocks cost \(O(n^3b^2\log(2n))\) together. This proves the uniform bound. More generally a division-free straight-line program manipulating input-field polynomials in one variable can be lifted gate by gate, at cost \(O(n^4\log(2n))\) per arithmetic gate. Its constant-polynomial gates supply the identically zero consequence.

The product identity holds also for simultaneous conjugacy of several matrices, with a word in the generators evaluated in the same order on both sides. Suppose each tuple consists of pairwise commuting matrices and the simultaneous split eigenvalue tuples have some difference in total algebraic multiplicity that is nonzero in the coefficient characteristic. Simultaneous triangularization over a splitting field supplies this multiset. Then binary PC on the directed intertwiner equations for the tuple and the two inverse families has a degree-two refutation of sparse size \(O(n^4\log^3(2n))\). This estimate counts only used lines and holds even if the number of supplied matrices exceeds \(n\).

To verify the last statement, take the finite signed measure with nonzero weights given by the visible differences on the distinct tuples. Its support size is at most \(2n\). If all coordinate projections on at most \(j\) coordinates have zero projected measure then a nonzero measure has support at least \(2^{j+1}\). For \(j=0\) this follows because the total weight is zero. For \(j>0\), choose a coordinate with at least two values on the support, which exists since a nonzero measure here has at least two support points. Each nonempty slice at a value of that coordinate has a nonzero weighted measure, and each projection of a slice on at most \(j-1\) other coordinates vanishes, by the hypothesis on projections that additionally retain the chosen coordinate. Induction gives \(2^j\) points in each slice. Consequently some projection on at most \(\lfloor\log_2(2n)\rfloor\) coordinates is nonzero. In each chosen coordinate, the one-variable Vandermonde basis up to degree one less than its number of values spans all functions of that coordinate. Tensor the bases on the full Cartesian product of their value sets. At least one monomial in this basis has nonzero weighted sum. That sum is the difference of the traces of the corresponding products of matrix powers, over the input field. Binary powering followed by at most \(\lfloor\log_2(2n)\rfloor\) product steps uses \(O(\log^2(2n))\) lifted gates. Applying the same trace identity gives the bound.

The theorems are written proofs. The first bound improves the prior general \(O(n^5\log(2n))\) sparse estimate on the full minimum-degree-two stratum. This applies in particular to dense matrices with equal ordinary trace whose characteristic polynomials can nevertheless be distinguished by traces of higher powers. [Prior sparse upper bound](QuinticUpper.md)
