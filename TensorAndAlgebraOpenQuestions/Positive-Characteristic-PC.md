# Positive-characteristic degree bounds for matrix isomorphism refutations

**Informal theorem.** Let \(M,N\) be explicit finite-dimensional representations of a finite quiver over a field \(F\) of characteristic \(p>0\). Suppose they are nonisomorphic over \(\overline F\). Pick an indecomposable isomorphism class occurring with different multiplicities \(a,b\) in the two decompositions over \(\overline F\), and put \(r=p^{v_p(|a-b|)}\). The ordinary Polynomial Calculus system for isomorphism with both inverse equations has a refutation of degree at most \(\max(3,2r)\) over \(F\). When \(r\) is bounded, the expanded size is polynomial in the explicit input. In particular the universal degree is at most \(\max(3,2d)\) for total dimension at most \(d\) on each side.

This applies to the exact conjugacy system in [Galesi–Grochow–Pitassi–She, Open Question 7.3](https://drops.dagstuhl.de/storage/00lipics/lipics-vol264-ccc2023/LIPIcs.CCC.2023.4/LIPIcs.CCC.2023.4.pdf), to simultaneous conjugacy, and to the stated congruence system in odd characteristic by the reduction below. This is an upper bound on degree and on size in the bounded-\(r\) regime. Optimal degree and unrestricted polynomial size are separate questions.

## Producing the rectangular inverse identities

Work first over \(\overline F\). Write the forward and reverse node maps as \(T\) and \(S\), with \(ST=I_M\), \(TS=I_N\). For an arrow \(A:M_t\to M_h\) and its target counterpart \(B:N_t\to N_h\), set \(E=T_hA-BT_t\). The identity
\[
S_hB-AS_t=S_hB(I-T_tS_t)-S_hES_t+(S_hT_h-I)AS_t
\]
derives the linear reverse intertwiner in degree 3. After these lines are derived, use linear projections \(P\) and \(Q\) from the spaces of all node maps to the two Hom spaces. The entries of \(T-P(T)\) and \(S-Q(S)\) are linear combinations of the available linear intertwiner equations. Multiplying those lines by linear expressions and adding the original inverse equations gives
\[
Q(S)P(T)=I_M,\qquad P(T)Q(S)=I_N
\]
as available quadratic lines, still within degree 3. For example \(ST-Q(S)P(T)=(S-Q(S))T+Q(S)(T-P(T))\).

View both projected maps in \(\operatorname{End}(M\oplus N)\). For the selected indecomposable class, take the corresponding matrix factor of the semisimple quotient of this endomorphism algebra. By Krull–Schmidt and the local endomorphism rings of the summands, that factor is \(\operatorname{Mat}_{a+b}(\overline F)\). The two summand idempotents give complementary blocks of ranks \(a,b\). The projected maps become rectangular matrices \(U,V\) of linear forms, and applying the linear block quotient to the available quadratic lines gives \(UV=I_a\) and \(VU=I_b\). This use of the quotient involves no new proof variables.

## Recovering the first differing base-\(p\) digit

For a square matrix \(Z\), let \(D_r(Z)\) be the sum of its principal \(r\)-minors, with value zero if the size is less than \(r\). Cauchy–Binet gives the polynomial identity \(D_r(UV)=D_r(VU)\) even for rectangular \(U,V\), since both expressions sum the same products of paired minors. Entry-by-entry telescoping in the determinant expansion derives \(D_r(UV)-D_r(I_a)\) from the available quadratic lines \(UV-I_a\) in degree at most \(2r\). Each multiplier has degree at most \(2r-2\), and the same argument applies to \(VU-I_b\). These derived lines give the constant \(\binom{a}{r}-\binom{b}{r}\). It is nonzero modulo \(p\) by the base-\(p\) binomial identity, because \(v_p(a-b)\) is the first position where the digits differ. Scale it to 1. The earlier degree-3 derivations of linear intertwiners need only be performed once.

To descend the degree bound to \(F\), let \(V_D\) be the finite-dimensional space of all polynomials of degree at most \(D=\max(3,2r)\) in the original variables. Start with the span of the axioms and iterate the operation of adjoining every variable multiple of every element in its intersection with \(V_{D-1}\). This computes exactly the degree-\(D\) PC span. Spans and intersections of finite-dimensional linear subspaces commute with field extension, so the derivation of 1 over \(\overline F\) implies derivability over \(F\). When \(D\) is constant, the ambient monomial count is polynomial. Row reduction and storing an available basis at every step give polynomial expanded proof size over \(F\).

## Congruence in odd characteristic

Use the two-vertex quiver with labelled arrows \(A_i,A_i^T\), and likewise for \(B\). Over an algebraically closed field of odd characteristic, simultaneous strict equivalence of the transpose pairs implies congruence. Indeed, if \(RA_iS=B_i\) and \(RA_i^TS=B_i^T\), then \(P=SR^{-T}\) satisfies \(A_iP=P^TA_i\). An invertible \(P\) has a polynomial square root \(H\), obtained on each primary factor by lifting a square root of the nonzero eigenvalue and dividing by twice that root. Then \(A_iH=H^TA_i\) and \(RH^T\) is a simultaneous congruence witness.

For a purported congruence \(X\) with inverse \(Y\), write \(C_i=XA_iX^T-B_i\). The forward and reverse linear intertwiner lines have degree-3 derivations from
\[
XA_i-B_iY^T=C_iY^T-XA_i(YX-I)^T,\qquad
YB_i-A_iX^T=(YX-I)A_iX^T-YC_i.
\]
Apply these formulas also to the transposed input. The quiver maps are \(Y^T,X\) in the forward direction and \(X^T,Y\) in the reverse direction. Their inverse identities are the original inverse equations and their transposes. Hence all subsequent lines of the proof work in the original variables with the same degree bound, using the indecomposable multiplicities of the transpose-pair quiver. This includes arbitrary labelled tuples, whether or not individual matrices are singular or symmetric.

**Attribution and scope.** The earlier MathProofs argument uses cyclic trace to detect multiplicity differences in characteristic zero. The new step replaces trace by the appropriate principal-minor coefficient and applies it in every semisimple block, extending the earlier compound argument for rectangular kernel obstructions. No claim of publication priority, optimality, or a characteristic-two congruence reduction is made.
