INDEPENDENT AUDIT: UNIVERSAL QUIVER / CONGRUENCE TRACE CERTIFICATES
Reviewer: Independent AI reviewer 1. November 4, 2026.
Informal mathematical audit; no Lean or publication-priority certificate.

FROZEN SOURCES READ
quiver-generic/UNIVERSAL-INTERTWINER.txt
SHA256 046955c452cac998196de0ec45b828a911153fc546539bf9f251e39cba17413b
quiver-generic/PC-DEGREE3-REFINEMENT.txt
SHA256 f2c494571b2bccc28ccf1f7da493770f61eb4a71576ee3a6d18e5efbdc692837
Also read matrix-pc/PROOF.txt for the kernel/compound refinement.

RESULT
No mathematical gap found in the degree-4 Nullstellensatz certificate or the stronger sequential degree-3 ordinary Polynomial Calculus theorem, within the exact stated field/input scope. The characteristic-zero matrix conjugacy and transpose-congruence systems have polynomial expanded-size degree-3 PC refutations whenever unsatisfiable over the algebraic closure. The finite-quiver theorem is similarly valid in characteristic zero or p greater than the stated total-dimension bound. The congruence argument needs characteristic different from two, supplied by its stronger p>2n hypothesis. No unrestricted TI / arrow-basis mixing claim follows.

1. EXACT ORIGINAL ENCODING / FIELD SCOPE
I checked CCC2023 Open Question 7.3 directly in the primary paper, page4:36. It explicitly includes BOTH XX'=I and X'X=I. Thus the draft's two-sided inverse axioms do match the source question; no inverse implication is supplied for free. The same paper defines PC degree as the maximum actual degree of a polynomial line, which justifies the sequential refinement below.

Algebraic-closure unsatisfiability is essential for congruence. For example [1] and [-1] are noncongruent over R but congruent over C; [1] and [2] behave similarly over Q versus its algebraic closure. Those examples are correctly excluded by the draft. No field equations or real positivity inference is hidden in the result.

2. THE SEPARATING ENDOMORPHISM TRACE
Finite-dimensional representations of a finite quiver, even with cycles, have Krull--Schmidt decompositions: finite vector-space dimension gives the required finite-length/Fitting properties. Endomorphism algebras are finite-dimensional. Over an algebraic closure, the residue division algebra of an indecomposable endomorphism algebra is the ground field, giving the product of full matrix algebras in the semisimple quotient of End(M directsum N).

Nonisomorphic M,N have different indecomposable multiplicities. In the corresponding semisimple factor, the two summand idempotents have ranks m_i,n_i. Its matrix trace kills commutators and distinguishes the idempotents by m_i-n_i. This is nonzero in characteristic zero, or when p exceeds the maximum total representation dimension. The functional is extended linearly to ambient endomorphisms, but its cyclicity is only invoked on products of genuine quiver endomorphisms. That restriction is respected throughout.

For the degree-3 refinement, choose the functional over F by solving the finite F-linear system tau([b_i,b_j])=0 and tau(e-f)=1 on an F-basis of the endomorphism algebra. Scalar extension commutes with the defining linear intertwiner kernels, so existence over the algebraic closure proves consistency over F. Ordinary row reduction then gives an F-valued solution. This avoids an unbounded splitting-field output or an invalid multiplicative use of coefficient descent. Hom projections can also be chosen over F.

3. THE BILINEAR IDENTITY AND REVERSE TRANSPORT
With u=t-t0 and v=s-s0, direct expansion verifies

 st-ts-(s0t0-t0s0)=vt+s0u-us-t0v.

All terms contain one residual and one linear variable expression. The Hom-space projections have residuals factoring linearly through the forward/reverse intertwiner maps, so the resulting certificate uses each linear intertwiner equation only with a linear multiplier. Genuine Hom commutators are killed by tau, term-by-term in fixed bases. The inverse defects give st=e+G and ts=f+F, yielding the claimed nonzero constant and degree-2 bidirectional certificate.

The matrix identity

 M_a S_t-S_h N_a=S_h E_a S_t-G_h M_a S_t+S_h N_a F_t

has correct dimensions and expands exactly. It derives the reverse H entries with degree-3 intermediates using both supplied inverse sides. No semantic cancellation or PC+Inv rule is needed. Substituting this identity into the expanded bilinear certificate gives the stated degree-4 Nullstellensatz certificate.

4. TRANSPOSE-PAIR STRICT EQUIVALENCE / CONGRUENCE
Suppose B_i=R A_i S and B_i^T=R A_i^T S with R,S invertible. Transposing the second equality and comparing gives A_i P=P^T A_i for P=S R^{-T}. Because P is invertible, its minimal polynomial has no zero root. Over an algebraically closed field of characteristic not two, primary-factor lifting solves h(t)^2=t modulo each primary factor, dividing only by twice a nonzero chosen square root; CRT combines them. Thus H=h(P) is a polynomial square root without any diagonalizability or nonsingularity assumption on A_i.

Functional calculus yields A_i H=H^T A_i. Then Z=R H^T satisfies Z A_i Z^T=B_i simultaneously. This proves the exact reduction for arbitrary singular and nonsymmetric labelled tuples. It concerns transpose congruence, not Hermitian congruence or base-field Witt classes.

5. DIRECT CONGRUENCE DEGREE ACCOUNTING
The identities

 XA_i-B_iY^T=C_iY^T-XA_iG0^T,
 YB_i-A_iX^T=G0 A_iX^T-YC_i

expand exactly and derive actual LINEAR forward/reverse pencil intertwiner lines with degree-3 intermediates. The transpose-pair versions follow from transposed C_i entries by field-linear combination. The pencil node maps are (Y^T,X), with reverse maps (X^T,Y); their two inverse defects are exactly source F0,G0 or transposes. No new variables or uncharged inverse axiom enters.

After those actual linear lines have been established, ordinary PC multiplies the FINAL lines by proof variables. Such new lines have degree two. The earlier derivation lines still have maximum degree three, but are never multiplied anew. Hence the complete sequential PC proof has degree at most three. Expanding the same derivations into a single source-equation Nullstellensatz identity instead yields degree at most four. The measures are correctly distinguished.

6. SIZE / EFFECTIVE CONSTRUCTION
The endomorphism basis, commutator constraints, normalized functional, Hom projections and residual maps are obtained by polynomial-size linear algebra in the actual explicit dimensions. There are polynomially many degree-3 expanded monomials and source equations. Over Q, all these constant linear systems have polynomial-bit rational data and solutions obtainable by exact elimination. Over arbitrary unspecified fields, the stated algebraic arithmetic convention remains necessary. No binary-compressed-dimension size claim is inferred.

The older kernel proof has the same sequential improvement: W is an actual linear line derived using degree three, so multiplying it by X entries creates quadratic lines, not degree-four ones. The quadratic UP=I and PU=I lines are then available. Multiplying them by compound cofactors of degree 2d-2 costs actual degree 2d; prior preparation contributes degree three. Thus max(3,2d) is the appropriate sequential compound bound. This does not supply matching lower bounds or polynomial size for exponentially large compound dimensions.

7. NONCLAIMS AND MINOR EDITORIAL POINT
No new symbolic controls were needed for this peer audit: I checked the displayed identities algebraically and read the owner reports separately, without treating smoke tests as a universal proof. Existing owner finite controls remain independent evidence. Optimal degrees, arbitrary small characteristic and publication priority remain unresolved.

In refinement Section 2 the phrase 'incorrect tighter accounting' should read 'unnecessarily looser accounting': multiplying the whole preparation gives a VALID but weaker degree-four PC upper bound. This is editorial, not a mathematical objection. The frozen source is unedited by this reviewer.

Primary statement and PC convention:
https://drops.dagstuhl.de/storage/00lipics/lipics-vol264-ccc2023/LIPIcs.CCC.2023.4/LIPIcs.CCC.2023.4.pdf


ADDENDUM: FINAL COSMETIC REBIND AND CONGRUENCE SHARPNESS AUDIT
Final PC-DEGREE3-REFINEMENT.txt SHA256:
b31cbe226438c634dde2d061373676d12fc4d115587a60564b56291bda1e39c8
An exact reverse byte replacement of 'unnecessarily looser accounting' by the old phrase 'incorrect tighter accounting' reproduces the previously audited SHA f2c494571b2bccc28ccf1f7da493770f61eb4a71576ee3a6d18e5efbdc692837. Thus this is a verified editorial-only change, and the preceding mathematical audit applies unchanged.

Also read quiver-generic/SHARPNESS.txt in full, SHA256:
c80da09e1af9632a03c63642a71ac5ac3abbfe56e5d3ca405450b46e1a22fd71
No mathematical gap found. The nonsymmetric 2 by 2 source equations and 5/3,1/3 moments expand correctly; the skew-part determinant contradiction excludes algebraic congruence in characteristic zero. Padding preserves nonsingularity of the relevant top-left block and the extended moment assignment annihilates all congruence/inverse entries. The even-degree source-span argument proves a genuine degree-two PC lower bound, not merely a Nullstellensatz lower bound. The scalar x^2=0,xy-1=0 example and its degree-three derivation are valid. The simpler A=I_n,B=0 family has the stated lower bound in every dimension. Combined with the universal characteristic-zero PC3 upper bound, this proves exact worst-case congruence degree three for every n>=1 within the documented algebraic-closure scope.

No kernel or priority certification is added by this addendum.


Later sharpness appendices establish exact degree 3 for congruence in every dimension and conjugacy from dimension 4; the older review above predates those appendices. The editorial accounting correction was applied in the final refinement. See the appended proofs and their separate exact controls.
