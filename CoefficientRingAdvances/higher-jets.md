# Higher scaling jets over the original coefficient field

**Theorem.** Let \(E\) be a finite field of characteristic \(p\), and let \(R=E\oplus J\) be a finite commutative local \(E\)-algebra given by structure constants and a grading by \(\mathbb N^t\). Assume \(R_{\mathbf 0}=E\), and that for each nonzero supported grade \(\lambda\), some coordinate \(\lambda_j\) is not divisible by \(p^{h+1}\). A principal determinant is \(\rho(G)=\det_R(G)/\det_E(\bar G)\). Prescribing the principal determinants of three-mode transporters reduces to one ordinary TI instance over \(E\), in polynomial time for fixed \(p,h\), with no bound on the nilpotence index of \(J\). Each mode may have any rank.

In particular this gives full determinant-one TI to ordinary binary TI for \(\mathbb F_2[x_1,\ldots,x_t]/(x_i^{2^{h+1}})\) and its proper monomial quotients, uniformly for fixed \(h\) and unbounded \(t\) in the explicit algebra presentation. For \(h\ge1\), the example includes the unit \(1+x_1^2\), missed by every ordinary derivation, and the unquotiented family has radical nilpotence index \(1+t(2^{h+1}-1)\).

**Relative determinant marker.** Let \(\alpha,\beta:R\to S\) be \(E\)-algebra homomorphisms with equal reductions modulo an ideal \(I\subset S\) satisfying \(I^{b+1}=0\). Regard the two copies of \(S^n\) as base changes along \(\alpha,\beta\), using the displayed map from the original \(R^n\) in each case. The corresponding induced actions are \(\alpha(G),\beta(G)\). Include their evaluations and pin the coefficient roles. On the space
\[
W=E\,1_n+\operatorname{Mat}_n(I)
\]
the induced action \(X\mapsto\alpha(G)X\beta(G)^{-1}\) preserves the scalar coefficient \(c\) of \(X=c1_n+N\). The same truncated determinant argument as in the coefficient-ring theorem applies. For \(r=\min(n,b)\), set
\[
P(c,N)=\sum_{j=0}^r c^{r-j}e_j(N).
\]
Here \(e_j\) is the sum of principal \(j\)-minors. Its formal coefficient vector transforms by the unit \(\alpha(\det_R G)/\beta(\det_R G)\). Indeed \(\det_S X=c^{n-r}P(c,N)\) over the formal polynomial ring. The displayed relative action multiplies the determinant by that unit and preserves \(c\), and cancellation of \(c^{n-r}\) is valid in a formal polynomial ring over any coefficient ring. Impose the prescribed scalar covariance by a coefficient mark and symmetric multiplication through degree \(r\). Since \(P(1,0)=1\), this reads the relative determinant exactly. Formal symmetric powers here use the polynomial coordinates, with no polarization or factorial division. [Earlier bounded-depth coefficient marker](https://github.com/Dugongue/MathProofs/blob/main/TISLCrossWorlds/CoefficientRings.md).

**Apply the marker to scaling.** Set \(b=p^h\), \(S=R[z]/(z^{b+1})\), \(I=(z)\), and let \(\beta\) be inclusion. For each coordinate \(j\) use the map
\[
\alpha_j(x)=(1+z)^{\lambda_j}x\quad\text{on }R_\lambda.
\]
Graded multiplication makes it an algebra homomorphism. A positive integer \(u=p^v u'\), \(p\nmid u'\), has
\[
(1+z)^u=(1+z^{p^v})^{u'},
\]
whose first nonconstant term is \(u'z^{p^v}\). Thus for each nonzero grade, some scaling detects the grade within the chosen truncation. By direct sum of homogeneous components, the common equalizer of the \(\alpha_j\) and \(\beta\) is exactly \(E\). To impose \(\rho(G)=\delta\), impose \(\alpha_j(\det G)/\beta(\det G)=\alpha_j(\delta)/\beta(\delta)\) for all \(j\). Their conjunction requires \(\det G/\delta\in E^\times\), equivalent to the claimed condition. All constraints are placed in the same tensor system, so they use the same transporter.

For an explicitly varying grading, there are as many copies as the input has grading coordinates. The degree \(b\) is fixed, the formal coefficient spaces have polynomial size, and binary grade labels are handled by repeated powering in the jet algebra. The free-module packing remains polynomial with a polynomial number of roles: its scalar copies, projection corners and rank labels grow polynomially in the number and ranks of the roles. This gives one ordinary TI output. In the binary scalar-residue case the residual determinant is automatically one. [Tensor-system packing](https://github.com/Dugongue/MathProofs/blob/main/IsomorphismCohomologyCrossovers/LinearLengthRings.md).



**Same-base mixed-characteristic extension.** Let \(A\) be a finite commutative local ring of characteristic \(p^s\), and let \(R\) be finite free in each homogeneous grade, with degree-zero part \(A\) and the same grading condition. The construction also reduces determinant comparison modulo the constant units \(A^\times\) to one ordinary free-module TI instance over \(A\), even for varying \(s\). In the relative marker replace \(E\,1_n\) by \(A\,1_n\). All displayed modules remain free over \(A\), and the same formal determinant and evaluation calculation applies. For a grade detected by coordinate \(j\), put \(v=\nu_p(\lambda_j)\le h\). The coefficient of \(z^{p^v}\) in \((1+z)^{\lambda_j}\) is nonzero modulo \(p\), by the characteristic-\(p\) computation above, so it is an integer unit in \(A\). Equality of the scaling and inclusion maps on \(R_\lambda\) again forces its element to vanish. The common equalizer is therefore \(A\), giving the claimed condition without increasing the coefficient precision at bounded \(h\).



For each fixed \(E\) and \(h\), the full special-linear problem over this explicitly graded family reduces uniformly to ordinary \(E\)-TI if the same-field collapse holds over \(E\). Retain the actual induced residue maps in the jet system with all principal targets one. Apply the fixed finite list of residue-character tests from the coefficient-ring theorem to that same system, followed by ordinary conjunction. The tests are valid on a common transporter because the residue determinant image is a coset. Conversely the family includes \(E\) by putting all coefficients in grade zero, so the uniform assertion implies the same-field collapse over \(E\). [Residue-character transfer](https://github.com/Dugongue/MathProofs/blob/main/TISLCrossWorlds/CoefficientRings.md).
