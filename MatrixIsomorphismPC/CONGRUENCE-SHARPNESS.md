# SHARPNESS OF THE UNIVERSAL MATRIX-CONGRUENCE PC BOUND

Informal proof, November 4, 2026. This appendix includes the upper theorem by reference and an explicit matching lower-bound family. No Lean verification or publication-priority certification.

THEOREM. Over every characteristic-zero field F, the worst-case ordinary PC refutation degree of the matrix-congruence system
 X A X^T-B=0, XY-I=0, YX-I=0
among algebraically-closed-field-UNSAT n-by-n instances is exactly 3, for every n>=1. Expanded refutations of polynomial size exist. The n=1 case is established explicitly in Section 5.

The upper bound and polynomial size are exactly Theorem C of TRACE-CERTIFICATE.md, sharpened by PROOF.md. Their field scope is unsatisfiability over the algebraic closure, not base-field signature/squareclass distinctions. We prove the matching degree-3 lower bound below.

1. An algebraically noncongruent 2-by-2 pair
Let
 A=[0 1;-2 0], B=[0 1;-3 0], J=[0 1;-1 0].
Suppose X A X^T=B for an invertible X over the algebraic closure. Skew parts give
 X(A-A^T)X^T=B-B^T,
 so 3 X J X^T=4 J. The elementary 2-by-2 identity X J X^T=(det X)J gives 3 det X=4.
On the other hand det A=2 and det B=3, so determinants give 2(det X)^2=3. Combining yields 32/9=3, i.e. 5=0, impossible in characteristic zero. Thus the ordinary algebraic system is unsatisfiable.

2. A degree-2 pseudoexpectation
Write X=[x y;z w], Y=[u v;r s]. The four congruence equations are
 -xy=0,
 xw-2yz-1=0,
 yz-2xw+3=0,
 -zw=0.
Define an F-linear functional L on polynomials of total degree at most 2. Put
 L(1)=1, L(xw)=5/3, L(yz)=1/3,
 L(X_ij Y_kl)=delta_{i,l} delta_{j,k}/2,
and let all other degree-1 and degree-2 monomials have value zero. These prescriptions do not conflict: the two specified X-X monomials and the X-Y monomials are distinct.

Then L annihilates every congruence equation, since 5/3-2/3-1=0 and 1/3-10/3+3=0. Also
 L((XY)_ij)=sum_k delta_{i,j} delta_{k,k}/2=delta_{i,j},
 L((YX)_ij)=delta_{i,j}.
Therefore it annihilates all eight inverse equations as well. In particular 1 is not in the F-linear span of the source equations.

3. Why this is a PC degree lower bound, not merely an NS lower bound
Every source polynomial has only degrees 0 and 2: no linear or odd-degree term occurs. Any F-linear combination of such polynomials has the same property. Before a nonzero constant is derived, every nonzero line in their span has degree exactly 2. Multiplying such a polynomial by any proof variable produces degree exactly 3 in a polynomial ring over a field, hence is forbidden in a degree-at-most-2 PC proof. A zero line yields nothing useful. No linear polynomial can be created by linear combinations of even polynomials. Thus every line of a degree-2 PC proof must remain in the source linear span unless the refutation has already occurred.

The functional L shows that no nonzero constant can be in that span: it annihilates the span but sends 1 to 1. Hence no degree-2 PC refutation exists. The upper degree 3 is therefore attained on this pair. Ordinary PC is intended throughout; no Boolean or field equations are adjoined.

4. Uniform padding gives sharpness for every n>=2
Let A_n=A directsum 0_{n-2}, B_n=B directsum 0_{n-2}. Any putative congruence X A_n X^T=B_n has top-left 2-by-2 block P A P^T=B, where P is the top-left 2-by-2 block of X. Because B and A are nonsingular, this forces P invertible, contradicting Section 1. Thus the padded instances remain algebraically unsatisfiable.

Extend L to the larger variable set as follows. On the first 2-by-2 X block retain the same two X-X moments, and set every other X-X moment to zero. Retain the first 2-by-2 X-Y moments from Section 2. For each i>=3 set L(X_ii Y_ii)=1. Set every other X-Y moment, every Y-Y moment and every linear moment to zero; keep L(1)=1.

Every congruence polynomial outside the top-left 2-by-2 block contains an X-X monomial involving a row index outside that block, so its expectation is zero, matching the zero entries of B_n. The first block is unchanged. In both XY and YX, the first two diagonal expectations equal 1 by Section 2, each remaining diagonal expectation equals 1 by its added diagonal moment, and every off-diagonal expectation is zero. Hence L annihilates every padded inverse equation. The same even-degree PC argument excludes degree-2 refutations for every n>=2.

Together with the universal degree-3 construction, this proves the exact worst-case degree assertion. Polynomial expanded proof size follows from the upper theorem and does not require a size lower bound. The result does not settle arbitrary small characteristic or optimal degrees of matrix conjugacy.

5. The scalar case is also sharp
For n=1 take A=[1], B=[0]. The equations are x^2=0 and xy-1=0 (the two inverse equations coincide). Define L(1)=1, L(xy)=1, and all other degree-at-most-2 monomial values zero. It annihilates the source equations, so the same even-degree argument excludes degree-2 PC refutations. A degree-3 refutation is explicit: derive x^2 y from x^2 and x^2 y-x from xy-1, subtract to obtain x, multiply by y and subtract xy-1 to obtain 1. Thus the exact worst-case bound is 3 also for n=1.

A simpler sharp family in every dimension is A=I_n,B=0: set every X-X moment to zero and set L(X_ii Y_ii)=1 for each i, all other moments zero, with L(1)=1. Then L annihilates XX^T and both inverse errors. Rank preservation proves unsatisfiability. The preceding nonsymmetric family is retained to show that the universal result also has explicit nonsymmetric sharp examples; it is not needed to establish worst-case sharpness by itself.
