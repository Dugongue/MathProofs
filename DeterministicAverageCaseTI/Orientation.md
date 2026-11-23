# Deterministic near-full average-case orthogonal tensor transporters

Let \(K=\mathbb F_q\) be given in an explicit polynomial basis, with \(q\) odd. An orthogonal transporter from \(A\) to \(B\) in \(K^n\otimes K^n\otimes K^n\) is a triple from \(O(n,K)^3\) mapping \(A\) to \(B\). An orientation profile records the three determinants of every transporter. The prescribed profile \((1,1,1)\) tests special-orthogonal isomorphism.

**Theorem.** For each fixed positive integer \(s\) there is a deterministic, zero-error partial algorithm with an explicitly recognizable source class. On this class, for every target it outputs every orthogonal transporter and hence the exact orientation profile and every special-orthogonal transporter. A uniform random source belongs to the class with probability at least
\[
 1-\frac{1}{2(n+1)^s}
   -\frac34 q^{-n(n-1)/2}
   -(1-c_n(q))^{n-2}-\varepsilon_{\rm gen}(n,q)
 \qquad(n\ge3),
\]
where \(c_n(q)=\prod_{i=1}^n(1-q^{-i})\) and \(\varepsilon_{\rm gen}(n,q)=q^{-\Omega(n)}\) is the probability that two independent uniform \(n\)-by-\(n\) matrices fail to generate the full matrix algebra. With \(L=\lceil24(n+1)^{s+1}\rceil\), there are at most \(2L\) transporters. At fixed odd characteristic the algorithm is unconditional and uses \(\operatorname{poly}_s(n,\log q)\) bit operations. With the premise of complete deterministic factorization in degree \(d^{O(\log(d+1))}(\log q)^{O(1)}\) over explicitly represented finite fields, the bound over arbitrary odd \(q\) is \(n^{O(\log(n+1))}\operatorname{poly}_s(\log q)\).

For clarity, the polynomial-time recognition assertion uses fixed odd characteristic. Under the factoring premise recognition over arbitrary odd fields has the same quasipolynomial bound as the search algorithm. The density is a property of the source alone and applies simultaneously to all targets. The random source distribution is unchanged. The algorithm uses no internal randomness.

This applies the Gram-centralizer route in Li, Li, Qiao, Tao and Wang, version 2, Section 5. Their Theorem 5.6 aims for complete transporter output and failure probability \(O_s(n^{-s})\). Its Gram and residual tuple routines are randomized. The replacement here keeps the Gram route and its probability estimates, constructs the Gram coset by primary-module linear algebra, and solves the residual search on a directly audited one-dimensional Hom condition. [Li–Li–Qiao–Tao–Wang, Theorem 5.6 and Propositions 5.2–5.4](https://arxiv.org/html/2604.00591v2#S5)

## 1. Self-adjoint operators with a capped orthogonal centralizer

Here \(F\) is any explicitly represented finite field of odd characteristic, \(V\) is finite-dimensional over \(F\), and \(b\) is a nondegenerate symmetric form on \(V\). Let \(S\) be self-adjoint for \(b\). Given a positive integer \(L\), the algorithm below determines whether the orthogonal centralizer of \(S\) has more than \(L\) elements and lists it exactly otherwise. In the latter case, for any second \(S'\) self-adjoint for \(b'\) on the same dimension, it either constructs one intertwining isometry \((V,b,S)\to(V',b',S')\) or decides that none exists. Its cost is polynomial in \(L,\dim_F V,\log |F|\) apart from polynomially many factorizations of degree at most \(\max(2,\dim_F V)\), over the original field \(F\). The construction includes zero, singular, repeated-root, and nonsemisimple operators.

### Primary cyclic summands and their residual forms

Factor the characteristic polynomial. Decompose into primary spaces \(V_f\) by kernels of powers of the irreducible polynomials \(f(S)\). Distinct primary spaces are orthogonal. For example, on \(V_g\) with \(g\ne f\), \(f(S)\) is invertible. Write any \(w\in V_g\) as \(f(S)^e w'\), where \(f(S)^e\) kills \(V_f\), and move \(f(S)^e\) across the pairing. The orthogonal summands \(V_f\) are therefore nondegenerate.

On \(V_f\), let \(e\ge1\) be the nilpotent exponent of \(f(S)\). The symmetric pairing
\[
 (u,v)\longmapsto b(u,f(S)^{e-1}v)
\]
is nonzero. Test the values on every basis vector and the sum of each pair of basis vectors. At least one is nonzero on the diagonal by polarization in odd characteristic. Choose the corresponding \(v\). Its cyclic \(F[t]\)-module is isomorphic to \(R_e=F[t]/(f^e)\), with \(t\) acting by \(S\), because \(f(S)^{e-1}v\ne0\). The restricted form on the cyclic summand is \(\ell(ab)\) for \(\ell(a)=b(v,av)\). Its radical is an ideal of \(R_e\). Any nonzero ideal contains \(f^{e-1}R_e\), on which \(\ell\) is nonzero by construction. The cyclic summand is thus nondegenerate. Its orthogonal complement is stable under \(S\). Iterate to obtain an explicit orthogonal decomposition by primary cyclic summands.

For each \(e\), let \(\lambda_e\) be the coefficient of \(t^{e\deg f-1}\) on the representative of degree less than \(e\deg f\) in \(R_e\). The pairing \(\lambda_e(ab)\) is nondegenerate: multiply a nonzero representative by a suitable power of \(t\) to bring its leading term to degree \(e\deg f-1\). Express each \(\ell\) uniquely as \(\lambda_e(\beta\,\cdot)\) by solving linear equations. The element \(\beta\in R_e\) is a unit, since a nonunit would give a nonzero radical in the pairing. Grouping equal exponents yields a diagonal invertible symmetric matrix \(H_{f,e}\) over \(R_e\) with \(m_{f,e}\) rows.

The group-by-exponent residue form \(\overline H_{f,e}\) over \(E_f=F[t]/(f)\) is intrinsic. Define
\[
 W_e=\ker f(S)^e\big/ \bigl(\ker f(S)^{e-1}
                     +f(S)\ker f(S)^{e+1}\bigr)
\]
on \(V_f\). This module is killed by \(f\). The pairing \(b(u,f(S)^{e-1}v)\) descends to \(W_e\), since vectors in the first summand of the denominator are killed by \(f(S)^{e-1}\), and moving the other factor of \(f(S)\) to \(v\) kills the second summand. On a cyclic summand of length less than \(e\) the numerator already equals the first denominator summand. On one of length greater than \(e\) it equals the second summand. A length-\(e\) summand contributes \(R_e/fR_e\), and
\[
 \lambda_e(f^{e-1}a)=\lambda_1(\bar a).
\]
This last identity follows from the monicity of \(f\). Thus the descended \(F\)-pairing is the transfer by \(\lambda_1\) of the \(E_f\)-bilinear form \(\overline H_{f,e}\). The transfer determines the \(E_f\)-valued form because \(\lambda_1(xy)\) is nondegenerate and the pairing is known on every \(E_f\) multiple of each vector. Every \(F[t]\)-linear isometry therefore preserves these residual forms.

Conversely, suppose the residual forms for \(S,b\) and \(S',b'\) can be matched by isometries over each \(E_f\). Lift the matching matrices to \(R_e\). After applying one such lift the new candidate Gram matrix \(H\) and desired \(H_0\) agree modulo \(f\). When they agree modulo \(f^j\), put \(D=H^{-1}(H_0-H)/2\). Then
\[
 (I+D)^{\mathsf T}H(I+D)=H_0+D^{\mathsf T}HD .
\]
The error lies in \(f^{2j}R_e\); the update is invertible and doubles precision. Iteration gives an exact \(R_e\)-isometry. Taking the direct sum across \((f,e)\) gives the required intertwining isometry. This proves classification and gives an explicit lift, even for nonsemisimple \(S\). [Sergeichuk, classification of self-adjoint operators and forms](https://arxiv.org/abs/0801.0823)

### Centralizer enumeration

Let \(\mathcal E=\operatorname{End}_{F[t]}(V)\), computed by commuting with \(S\), and let \(*\) denote the adjoint under \(b\). Taking the maps on all \(W_e\) gives a surjective homomorphism
\[
 \pi:\mathcal E\longrightarrow\prod_{f,e}M_{m_{f,e}}(E_f).
\]
With the cyclic decomposition, an arbitrary collection of residue maps lifts block diagonally as ordinary module endomorphisms, establishing surjectivity. The quotient involution is the adjoint in the residual forms, by the defining pairings on \(W_e\).

The ideal \(J=\ker\pi\) is nilpotent. Within one primary space, a module map from a cyclic summand of length \(a\) to one of length \(b\) carries its generator into \(f^{\max(0,b-a)}R_b\). If \(a=b\) and the map is a block of an element of \(J\), its image has an extra factor \(f\) by definition of \(\pi\). In a product of elements of \(J\), follow any path of summand lengths. At each weak increase the \(f\)-adic order increases by at least one. At a decreasing step it cannot go down unless the term becomes zero. If \(h\) is the largest length, every stretch of \(h\) steps contains a weak increase. Thus all paths in a product of \(h^2\) such factors vanish. Different primary components never mix.

The centralizer \(C=\{g\in\mathcal E:g^*g=1\}\) maps onto \(\prod_{f,e} O(\overline H_{f,e},E_f)\) by the same blockwise Newton lift. Its kernel is in bijection with the skew-adjoint vector space \(J^-=\{u\in J:u^*=-u\}\) via
\[
 u\longmapsto(1-u)(1+u)^{-1}.
\]
Indeed the map lands in \(1+J\) and is unitary by the adjoint identity. Its inverse is \(g\mapsto(1-g)(1+g)^{-1}\). Both inverses exist by nilpotence and the invertibility of 2. The kernel cardinality is \(|F|^{\dim_F J^-}\), obtained by linear algebra. Return over-cap immediately if it exceeds \(L\). Otherwise enumerate its elements with that cardinality. A lift of each residue tuple times each kernel element then gives the full centralizer. [Brooksbank and Wilson, Computing Isometry Groups of Hermitian Maps](https://doi.org/10.1090/S0002-9947-2011-05388-2)

It remains to bound residue computations without iterating through a potentially enormous extension. Let \(Q=|E_f|\) and \(m=m_{f,e}\). If \(m=1\), a residue orthogonal group gives exactly the signs. A residue isometry from the source line to a target line is a square root of the ratio of their form coefficients. The following procedure obtains that square root using only factorization over the original field \(F\). For a nonzero element \(a\in E_f\), compute the \(F\)-linear fixed space of the \(|F|\)-power map on \(B=E_f[Y]/(Y^2-a)\). Its dimension is one in the nonsquare case and two in the square case, by the field or product-of-two-fields description of \(B\). In the second case choose a nonscalar fixed element. Its degree-two minimal polynomial splits over \(F\). Factoring it separates the two primitive idempotents. Project the class of \(Y\) to one component and express it in the image of the explicit \(E_f\) basis by linear algebra. This gives the required square root in \(E_f\). If \(m\ge2\), each nonisotropic line defines a different orthogonal reflection, since that line is its negative eigenspace. The nonzero quadratic form has at most \(2Q^{m-1}\) zeros, so
\[
 |O(\overline H_{f,e},E_f)|\ \ge\ \frac{(Q-2)Q^{m-1}}{Q-1}
 \ \ge\ \frac12 Q^{m-1}.
\]
If this group has at most \(L\) elements, then \(Q\le2L\) and \(Q^m\le4L^2\). Test the latter inequality first and return over-cap if it fails. Otherwise all \(E_f^m\) vectors can be enumerated within the budget.

For enumerating the residue group, take an orthogonal basis of the source form via diagonalization and backtrack on its images, requiring the correct nonzero norms and orthogonality so far. Every such partial assignment extends to an isometry of the full space. Indeed the spanned spaces are nondegenerate and their complements have equal dimension and determinant square class. For the underlying classification, a diagonal nondegenerate binary form \(a x^2+b y^2\) represents every \(c\ne0\), because the sets \(a\{x^2\}\) and \(c-b\{y^2\}\) both have \((Q+1)/2\) elements. Splitting off norm-one lines inductively shows that dimension and determinant square class classify all nondegenerate forms. Thus more than \(L\) prefixes at any one depth already certify that the group exceeds the cap. Each retained depth has at most \(L\) prefixes and each scans at most \(4L^2\) candidate vectors. The very same search gives one residue isometry between two different forms if dimension and determinant square class match. Complements have matching classes at each depth, so each partial choice extends. Compare the product of all group cardinalities with the cap, including the radical kernel. All costs are bounded polynomially in \(L,\dim_F V,\log|F|\) in addition to the indicated factorization calls.

### Factoring over fixed characteristic

For completeness, complete factorization over an explicitly represented finite field of characteristic \(p\) has an elementary deterministic \(\operatorname{poly}(p,d,\log|F|)\)-time bound. On \(F[t]/(h)\) compute the \(\mathbb F_p\)-linear fixed space of the \(p\)-power map. On a local primary factor any fixed element is a scalar from \(\mathbb F_p\) plus a nilpotent, and that nilpotent vanishes under iterated \(p\)-powering. Thus the fixed algebra is \(\mathbb F_p^u\), one coordinate for each distinct irreducible factor. Take a linear basis. For each basis vector, refine each current factor by taking gcds with its representative minus each \(a\in\mathbb F_p\). These gcds retain the correct full primary powers. Every pair of coordinates is eventually separated, since a basis of the full product separates them. Each surviving factor is a power of one irreducible. Successive \(p\)-th-root extraction for zero derivative, with inverse Frobenius on coefficients, and then division by the derivative gcd recover its monic irreducible generator and multiplicity. This works over all residue extensions used above. At fixed characteristic it costs polynomial time, without the extrapolation of a prime-field-only algorithm to extension fields. [Berlekamp, Factoring Polynomials Over Large Finite Fields](https://www.ams.org/journals/mcom/1970-24-111/S0025-5718-1970-0276200-X/)

## 2. Replace both randomized steps of the tensor search

Use the first-mode flattening \(M_A\) and the standard form \(b\) with matrix \(I_n\). Set \(S_A=M_A M_A^{\mathsf T}\). Every orthogonal transporter has first factor \(P\) satisfying \(P S_A=S_B P\). This is exactly the single self-adjoint-operator comparison of Section 1. Define the source class by the two exact tests
\[
 |C_{O(n,K)}(S_A)|\le L,\qquad
 \dim_K\{(U,V): U A_i=A_i V\ \text{for all first-mode slices }A_i\}=1.
\]
The first test uses Section 1 and the second a Gaussian rank. The second test is invariant under all orthogonal basis changes: first-mode mixing preserves the linear span of the slices, and the other two changes transport the displayed system by invertible linear substitutions. Gram equivariance makes the first test invariant as well.

If there is no intertwining isometry for the Gram pair, the tensor pair has no orthogonal transporter. Otherwise obtain one first factor \(P_0\) and enumerate its right coset \(P_0 C_{O(n,K)}(S_A)\). For each \(P\) in the coset, undo it in the target first mode and write \(B'_i\) for the transformed slices. Solve the ordinary linear system
\[
   U A_i=B'_i V\quad\text{for every }i .
\]
A solution with \(U,V\) invertible induces an isomorphism of this solution space with the source endomorphism space by composition. Since the latter is a line, if the space has dimension other than one this candidate has no extension. Otherwise take its nonzero generator \((U_0,V_0)\). If either matrix is singular, no multiple can extend. In the invertible case test whether
\[
 U_0^{\mathsf T}U_0=V_0^{\mathsf T}V_0=\lambda I_n
\]
for one nonzero \(\lambda\). For this to hold after a common nonzero scaling, it is necessary to hold before scaling. If it holds, factor \(X^2-\lambda^{-1}\). Each of its base-field roots \(t\) gives the two orthogonal factors \(tU_0,tV_0\), and all factors arise this way. The linear system and the relations \(V^{-1}=V^{\mathsf T}\) give the original tensor equation. At most two extensions occur per Gram candidate. This removes the randomized residual tuple-isometry subroutine and the residual centralizer enumeration. Every result also checks directly in the original tensor equation and the three orthogonality conditions. Sorting the resulting triples by their determinants gives the orientation and the special-orthogonal answer.

An affirmative certificate is the transporter itself. A complete list or negative output has a deterministic replay certificate: give the characteristic factors, the cyclic bases and residue forms, the rank of the linear endomorphism test, the bounded Gram candidate list as enumerated above, and the residual rank or scalar test per candidate. Irreducibility of a putative degree-\(d\) characteristic factor can be checked by modular Frobenius and gcds for the prime divisors of \(d\). A missing scalar root is verified by the quadratic character test. The replay checks the enumerated residue vectors and the kernel basis and then recomputes the coset list. This verification is polynomial in \(n,L,\log q\), even when construction uses the quasipolynomial factoring premise.

## 3. Density and scope

Propositions 5.2 and 5.3 of Li–Li–Qiao–Tao–Wang give
\[
 \Pr_A[|C_{O(n,K)}(S_A)|>L]
 \le \frac{12(n+1)}{L}+\frac34 q^{-n(n-1)/2}.
\]
For the linear recognition test, if the first invertible slice occurs at \(j\le n-2\), then conditionally on this event and the slices through \(j\), \(A_j^{-1}A_{j+1}\) and \(A_j^{-1}A_{j+2}\) remain independent uniform matrices. When they generate the full algebra, \(U A_i=A_i V\) implies \(U=A_jVA_j^{-1}\) and \(V\) commutes with both generators. Then \(V\) is scalar and \(U=V\). Failure of this sufficient event has probability at most \((1-c_n(q))^{n-2}+\varepsilon_{\rm gen}(n,q)\), as in their Proposition 5.4. Taking a union bound proves the stated coverage. [Li–Li–Qiao–Tao–Wang, Propositions 5.2–5.4](https://arxiv.org/html/2604.00591v2#S5.SS2)

The source-class guarantee concerns the orthogonal action, and the determinant profile restricts its transporters. For ordinary \(GL^3\)-TI, the Gram conjugation identity used in Section 2 is unavailable. For ordinary \(SL^3\)-TI the determinant tests on this list consequently do not constitute a complete test. The earlier two-covariant recognized class already has a deterministic comparison mechanism and sign descent on its own hypothesis. The present contribution is deterministic complete enumeration on the single-Gram, capped-centralizer route at its stronger \(1-O_s(n^{-s})\) coverage for every fixed \(s\), with no independent draw after the source is sampled. Fixed characteristic uses only unconditional finite-field operations and the large characteristic result uses the stated factoring premise. An exact check over the fields of orders 3 and 5 compared the radical-and-residue centralizer formula with direct matrix enumeration for 881 symmetric matrices, including 280 nonsemisimple matrices and 24 positive-dimensional skew-adjoint radical spaces. The general argument is a written proof.
