# Unbounded-depth principal determinants via mixed-characteristic lifts

**Theorem.** Fix a prime \(p\) or supply it in binary. Let \(s\ge1\). Let \(B\) be an explicitly presented graded commutative algebra, finite free in each homogeneous grade over \(A=\mathbb Z/p^a\mathbb Z\), with degree-zero part \(A\) and only nonnegative grades. Put \(R=B/p^s B\). Suppose
\[
a\ \ge\ s+\max\{\nu_p(d):d>0,\ B_d\ne 0\}.
\]
Use maximum zero if there are no positive grades. For a matrix over \(R\), its principal determinant means its determinant divided by the constant term of the determinant, using the displayed scalar section. On free dense tensors over \(R\), ordinary transport with prescribed principal determinants in any modes reduces in deterministic polynomial bit time to one ordinary free-module tensor isomorphism instance over \(A\). All presented coefficient and lift data are charged to the input.

In particular, suppose \(R=(\mathbb Z/p^s\mathbb Z)[x_1,\ldots,x_t]/I\) is given by the finite standard-monomial basis of a monomial ideal \(I\) and its multiplication. A suitable \(B\) is obtained by keeping the monomial basis and multiplication at precision \(a\). For a truncated univariate ring of length \(e\ge2\), take \(a=s+\lfloor\log_p(e-1)\rfloor\). At \(s=1,p=2\), principal determinant one is the full determinant-one condition, since the degree-zero field has only one unit. Thus binary truncated polynomial rings of arbitrary length and binary monomial algebras of arbitrary depth admit the full reduction to ordinary TI at the displayed mixed-characteristic precision. The same proof allows a supplied finite free degree-zero extension of \(A\), using its unit group for the constant terms and restricting all free modules to \(A\).

**The precision identity.** Let \(D\) be the Euler derivation, acting as multiplication by \(d\) on \(B_d\). The normalized units \(u\) with degree-zero term one have unique finite factorizations
\[
u=\prod_{d>0}(1-x_d),\qquad x_d\in B_d.
\]
Choose \(x_d\) consecutively in increasing grade to match the degree-\(d\) component. Multiplication by later factors cannot change that component, and a grade with \(B_d=0\) uses \(x_d=0\). This also proves that the factors reduce coordinatewise modulo \(p^s\). Writing \(\ell(u)=D(u)/u\), the product rule and finite geometric series give
\[
[\ell(u)]_n=-\sum_{d\mid n}d\,x_d^{\,n/d}.
\tag{1}
\]
The formula is the Euler-product form of the big Witt ghost calculation. [Hesselholt, Sections 1–2](https://math.mit.edu/~larsh/papers/s03/wittsurvey.pdf).

If \(x\equiv y\bmod p^sB\), then \(x^m\equiv y^m\bmod p^{s+\nu_p(m)}B\). One \(p\)-th power gains a digit by the binomial formula for \(s\ge1\). Iterate and take the remaining prime-to-\(p\) power. In (1), multiplication by \(d\) raises that precision to \(s+\nu_p(n)\). Thus equal normalized units modulo \(p^s\) have equal ghosts at those respective precisions. Conversely, compare the factors in ascending grade. At grade \(n\) the proper-divisor terms already agree at precision \(s+\nu_p(n)\), and the remaining difference is \(-n(x_n-y_n)\). Freeness of \(B_n\) and invertibility of \(n/p^{\nu_p(n)}\) give \(x_n\equiv y_n\bmod p^sB_n\). This proves the converse. General units are handled by dividing out the degree-zero term, which the derivation kills.

Represent all precisions by a single explicit linear map \(F:B\to B\), zero on degree zero and with multiplier \(p^{a-s-\nu_p(n)}\) in positive degree \(n\). Because the homogeneous modules are free, \(F(\ell(u))=F(\ell(v))\) is exactly agreement of the corresponding normalized units modulo \(p^s\). The maps can be computed directly with binary grade labels. A dense index range through the maximum grade is unnecessary when the grading is sparse.

**One free-module tensor system.** Lift the input to the same free \(B\)-modules. Write \(W=B^n\) in one mode, and retain the coefficient multiplication actions and the source tensor multiplied by \(p^{a-s}\). The latter is a well-defined mark independent of the chosen lift. Because the ambient tensor module is free over \(A\), equality of marks is exactly equality of the input tensors modulo \(p^s\). Pin the \(A\)-basis of \(B\) and a scalar line. Use evaluation to force the natural action on the free \(A\)-space \(\operatorname{End}_A(W)\).

With \(D_W\) the coordinatewise Euler derivation, take the named free \(A\)-module
\[
C=\operatorname{Mat}_n(B)\oplus A
\]
with linear arrow \((M,t)\mapsto M+tD_W\) into \(\operatorname{End}_A(W)\) and a second arrow \((M,t)\mapsto t\) to the fixed scalar line. The pair of arrows is injective even if \(D_W\) has additive torsion. For a \(B\)-linear map \(G\), their preservation forces the map on \(C\) to be
\[
(M,t)\mapsto(GMG^{-1}-tD(G)G^{-1},t).
\]
This follows by differentiating the identity for \(G^{-1}\). Jacobi's determinant formula gives \(\operatorname{tr}(D(G)G^{-1})=\ell(\det G)\) over the commutative ring \(B\).

For the prescribed value \(\delta\), take any unit lift \(\widetilde\delta\). Include a linear arrow from \(C\) to the fixed \(B\) role. At the source it is \((M,t)\mapsto F(\operatorname{tr}M)\). At the target it is \((M,t)\mapsto F(\operatorname{tr}M)+tF(\ell(\widetilde\delta))\). Equivariance is exactly \(F(\ell(\det G))=F(\ell(\widetilde\delta))\), since trace is unchanged by \(GMG^{-1}\). The precision identity gives the prescribed principal determinant on reduction. Conversely, each permitted transporter over \(R\) lifts to invertible matrices over \(B\), since \(p^sB\) is nilpotent. Every such lift satisfies the arrow and the input tensor marks. The formula uses only free \(A\)-modules and does not impose any constraints on an arbitrary choice of lift beyond the original predicates.

The balanced tensor product is included using its explicit free \(B\)-basis and successive bilinear maps, whose values span. All the data are linear or bilinear arrows and vector marks on free \(A\)-modules. Their dimensions and coefficients are polynomial in the input and the displayed precision. The free-module tensor-system packing compiles these data to one ordinary 3TI instance over \(A\). The underlying first-order Jacobi construction and the free-module packing suffice for this mixed-characteristic compiler. [Earlier characteristic-\(p\) derivation construction](https://github.com/Dugongue/MathProofs/blob/main/LocalDeterminantTransfers/Compiler.md), [Free-module packing](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCohomologyCrossovers/LinearLengthRings.md), [Grochow–Qiao–Stange–Sun, Part V, Section 3.3](https://arxiv.org/html/2611.00735v1#S3.SS3).
