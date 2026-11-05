# Kernel Transport Certificates for Matrix Nonconjugacy

MathProofs, AI-assisted informal proof candidate, 2026-11-04.
No Lean verification or publication-priority claim.

1. Precise source and results

Galesi, Grochow, Pitassi and She, On the Algebraic Proof Complexity of Tensor Isomorphism, CCC 2023, Open Question 7.3, asks for PC degree and size of matrix conjugacy and matrix congruence. The conjugacy system for fixed A,B in Mat_n(F) is
  E = X A - B X = 0,  F0 = X Y - I_n = 0,  G0 = Y X - I_n = 0.
All n² entries of each displayed matrix are equations. Polynomial Calculus (PC) permits field-linear combinations and multiplication by a single proof variable. Multiplying a derived equation by an expanded polynomial means its monomial-by-monomial PC derivation. No Boolean/field equations or extra variables are assumed.

THEOREM A. If a polynomial f in F[t] has a=dim ker f(A), b=dim ker f(B), and a-b is nonzero as an element of F, the conjugacy system has a PC refutation of degree at most 4 and polynomial expanded size in n. In characteristic 0, or characteristic p>n, every nonconjugate pair satisfies this hypothesis for some f. Thus every nonconjugate pair over these fields has degree at most 4 and n^{O(1)}-size PC refutations, with no restrictions on eigenvalues, Jordan block sizes, cyclicity, or diagonalizability.

THEOREM B. In every characteristic, every nonconjugate pair has a PC refutation of degree at most 2n. In characteristic p, Theorem A’s construction can instead give degree at most 2d+2, where d=p^{v_p(a-b)} for any differing polynomial-kernel nullities a,b. Consequently the bound is the minimum of 2n and these kernel-dependent bounds. These are universal upper bounds; matching small-characteristic degree/size lower bounds are not proved here.

These theorems answer the characteristic 0/large-characteristic polynomial-size and constant-degree upper-bound part of the CONJUGACY question. They do not settle all of Open Question 7.3, its matrix-congruence half, or exact optimal degrees. PC tests unsatisfiability over the algebraic closure. Similarity of a single matrix descends to the coefficient field by rational canonical form, so no hidden field-descent promise is introduced.

Primary source:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol264-ccc2023/LIPIcs.CCC.2023.4/LIPIcs.CCC.2023.4.pdf

2. Inverse transport, with its actual PC cost

The following identity is an identity of matrices over F[X,Y]:
  A Y - Y B = Y E Y - G0 A Y + Y B F0.                  (2.1)
Every entry on the right is a sum of source equations multiplied by monomials of degree at most2. Thus AY-YB has a degree 3 PC derivation. We do NOT infer inverse transport by an uncharged semantic cancellation or by PC+Inv.

For f(t)=sum c_j t^j, telescoping gives
  X f(A)-f(B)X = sum_{j>=1} c_j sum_{h=0}^{j-1} B^h E A^{j-1-h}.
This is a scalar linear combination of E entries, so has degree 1. The corresponding f(A)Y-Yf(B) has degree 3 by (2.1). Although the polynomial f can have large degree, A,B and all their powers are CONSTANT matrices: their powers introduce no proof-variable degree.

3. Kernel-coordinate reduction

Choose fixed bases putting ker f(A) in the first a coordinates of the source and ker f(B) in the first b coordinates of the target. Use the invertible linear substitutions X_new=T_B^{-1}XT_A and Y_new=T_A^{-1}YT_B. Linear changes preserve the degree bound; expanding degree at most 4 preserves polynomial size.

Write rectangular blocks, allowing zero-sized blocks:
  X = [P Q; R S],       Y = [U V; W Z],
where P is b by a, U is a by b, R is (n-b) by a, and W is (n-a) by b.
Kernel transport implies R=0 with degree 1 and W=0 with degree 3. Here is the linear-algebra justification, without adding unproved kernel equations: columns in the source kernel have f(A)e_j=0. Multiplication of Xf(A)-f(B)X by these constant vectors yields f(B)Xe_j=0. A fixed left inverse of f(B) on a complement to its kernel recovers every coordinate of R as a scalar linear combination of these equations. The identical argument with inverse transport recovers W in degree 3.

The top-left blocks of the supplied inverse axioms give
  U P + V R = I_a,       P U + Q W = I_b.
Multiplying the already derived R entries by the relevant Y variables derives UP=I_a in degree 2. Multiplying W entries by the relevant X variables derives PU=I_b in degree 4. Cyclicity of rectangular trace is a polynomial identity:
  tr(UP)=sum_{i,j}u_ij p_ji=tr(PU).
Subtracting the traces of the last equations derives a-b=0. Divide by the nonzero field element a-b to obtain1=0. This proves the sufficient statement in Theorem A.

An explicit Nullstellensatz identity before substitution is
  a-b = tr(VR) - tr(QW) - tr((G0)_aa) + tr((F0)_bb).
Replacing R by its degree 1 E combinations and W by its degree 3 (2.1) combinations gives a certificate with every source-equation product of degree at most 4. This identity also proves the bound without invoking a generic PC proof-search algorithm.

4. Coverage of every nonconjugate pair in the stated fields

The F[t]-module associated to A is a direct sum of modules F[t]/(p(t)^e), for monic irreducibles p. The family of integers dim ker p(A)^k determines these elementary-divisor multiplicities: divide the successive differences in nullities by deg p to count the summands with e>=k, then take another difference. Therefore A and B are conjugate if and only if all these nullities agree. Any nonconjugate pair has an f=p^k with a!=b. One may take deg f<=n when n>0: the relevant exponent need not exceed the largest occurring p-primary block, whose dimension is at most n.

In characteristic 0 every nonzero integer remains nonzero in F. In characteristic p>n, 0<|a-b|<=n<p likewise remains nonzero. Theorem A therefore covers ALL nonconjugate pairs in these fields. This includes nilpotent matrices with identical characteristic polynomial and traces of all positive powers; a trace test on A alone would miss them. The proof instead traces the induced two-sided maps between polynomial kernels.

Each derivation above has a polynomial number of scalar matrix operations and proof-variable monomial products of degree at most 4. All matrices have order at most n, and polynomial f may have degree at most n. Fixed coordinate changes can expand a degree 4 monomial by at most (2n²)^4 terms. A deliberately loose n^{O(1)} expanded-size bound follows. This is an algebraic size bound, not a claim that arbitrary coefficient fields come with a uniform effective arithmetic implementation or that bit lengths are free over Q.

5. The universal degree 2n bound

Let J be the homogeneous linear ideal generated by entries of E. Its zero set over an algebraic closure is exactly the space of intertwiners. If A,B are nonconjugate, every intertwiner is singular, so det X vanishes on this linear space. A linear ideal is radical, and its quotient is a polynomial ring on a basis of that space. Hence det X lies in J, without taking any power. Homogeneity gives
  det X = sum_ij l_ij(X) E_ij
with deg l_ij<=n-1. This has a degree n PC derivation (arbitrarily large size is allowed for this degree assertion).

From XY-I=0, telescoping the determinant expression derives det(XY)-1 in degree at most 2n: in each determinant summand, replace its n entries of XY one at a time by the corresponding identity entries; every resulting product has degree at most 2n. The polynomial identity det(XY)=det X det Y is valid in every characteristic. Multiply the derived det X=0 by det Y, monomial by monomial, in degree 2n. Subtraction yields1. This proves Theorem B's universal degree bound, including small finite fields. No assumption that a polynomial function over a finite field is determined by its finite evaluations is made: the vanishing and radical argument is over its algebraic closure.

6. Characteristic-sensitive improvement via compounds

Take any a!=b as in Section 4. We have UP=I_a in degree 2 and PU=I_b in degree 4. For an integer d>=1, write C_d(P),C_d(U) for their d-th compound matrices, indexed by d-element row/column subsets; when d exceeds a dimension the corresponding matrix has zero rows or columns. Cauchy-Binet gives
  C_d(UP)=C_d(U)C_d(P),
  C_d(PU)=C_d(P)C_d(U).
Telescoping determinant entries using UP-I_a derives C_d(U)C_d(P)=I_binom(a,d) in degree at most 2d. Using PU-I_b instead costs at most 4+2(d-1)=2d+2. The identities are expanded polynomial identities, not new PC rules or new variables. Their rectangular traces then yield
  binom(a,d)-binom(b,d)=0
in degree 2d+2.

For characteristic p, choose j=v_p(a-b) and d=p^j. Lucas's congruence gives binom(a,p^j) equal to the j-th base-p digit of a modulo p, and analogously for b. All lower digits agree and the j-th differs, so this trace difference is nonzero. Moreover d<=max(a,b)<=n. This yields the characteristic-sensitive upper bound in Theorem B. Compound matrices can have exponentially many entries when d grows, so this last bound does not claim polynomial proof size uniformly in p or d.

7. Attribution, reuse and verification status

The CCC 2023 problem statement, PC convention, and distinction from PC+Inv are due to Galesi, Grochow, Pitassi and She. Kernel classification of single-matrix conjugacy, rectangular trace, determinant identities, compound matrices/Cauchy-Binet, and Lucas's congruence are classical tools, not discoveries claimed here. Our existing MathProofs PC-bridge notes supplied the discipline of charging both inverse equations and expanded monomial products; the shared source/notes catalogue was searched across all 63 currently registered catalogue providers. Mathlib's matrix trace and determinant sources were inspected as mathematical interfaces. Source-only search hits are not Lean verification.

The contribution offered here is the explicit kernel-transport PC derivation with its scope and degree accounting. Internal review and finite exact controls cannot establish first-publication priority or replace a kernel-checked proof. No source code from upstream libraries is copied into this informal document.
