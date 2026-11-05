# EXACT DEGREE-3 CONJUGACY REFUTATIONS: A MATCHING LOWER-BOUND FAMILY

Informal proof, November 4, 2026. No Lean verification or priority claim.

THEOREM
For every field F, there exist fixed nonconjugate 4 by 4 matrices whose ordinary Polynomial Calculus conjugacy system has refutation degree exactly three. The same holds in every dimension n>=4 by zero-block padding. Consequently the universal characteristic-zero degree-three upper bound in PROOF.md is sharp in the worst case.

Use the exact CCC 2023 Open Question 7.3 source system:
 E=XA-BX=0, F0=XY-I=0, G0=YX-I=0,
with all matrix entries as equations and no extra axioms.

Let J2=[0 1;0 0], A=J2 directsum J2, and B=J2 directsum[0]directsum[0]. Their ranks are two and one over every field, so they are not conjugate.

1. AN INTERTWINER PARAMETRIZATION
Make the homogeneous linear substitution

 X=[a c b d;
    0 a 0 b;
    0 e 0 f;
    0 g 0 h],

leaving all sixteen entries y_ij of Y free. Direct multiplication gives XA-BX=0 identically. Thus any degree-two PC refutation of the original system would yield a degree-two PC refutation of the substituted inverse system. A linear substitution of proof variables is simulated by field-linear combinations of ordinary variable multiplications and never increases degree.

2. AN EXPLICIT LINEAR FUNCTIONAL ON DEGREE-TWO POLYNOMIALS
Define ell(1)=1. Set every degree-one monomial, every product of two a,...,h parameters, every product of two Y entries, and all cross monomials except the following to zero:

 ell(a y11)=1,
 ell(b y31)=1,
 ell(b y42)=1,
 ell(c y21)=-1,
 ell(e y23)=1,
 ell(g y24)=1.

Extend ell linearly over F. These are integer values and the identities hold in every characteristic, including characteristic two.

Checking the diagonals of XY:
 ell((XY)11)=ell(a y11+c y21+b y31+d y41)=1-1+1=1;
 ell((XY)22)=ell(a y22+b y42)=1;
 ell((XY)33)=ell(e y23+f y43)=1;
 ell((XY)44)=ell(g y24+h y44)=1.
All off-diagonal XY entries have value zero.

Checking the diagonals of YX:
 ell((YX)11)=ell(y11 a)=1;
 ell((YX)22)=ell(y21 c+y22 a+y23 e+y24 g)=-1+0+1+1=1;
 ell((YX)33)=ell(y31 b)=1;
 ell((YX)44)=ell(y41 d+y42 b+y43 f+y44 h)=1.
All off-diagonal YX entries have value zero. Thus ell annihilates every entry of both substituted inverse defects, while ell(1)=1.

3. WHY THIS EXCLUDES DEGREE-TWO PC, NOT ONLY DEGREE-TWO NULLSTELLENSATZ
Every nonzero substituted source equation is a homogeneous quadratic plus a constant. Therefore their linear span V has no degree-one terms. It contains no nonzero constant: applying ell to a putative constant in V gives zero, while ell of that constant equals the constant itself.

Hence every nonzero polynomial in V has actual degree exactly two. A degree-two PC derivation cannot multiply such a polynomial by a variable, because the resulting polynomial has a nonzero degree-three leading part. Its multiplication rule can therefore act only on zero lines. Induction on the proof shows that every degree-at-most-two derived line lies in V. In particular it cannot produce 1. This closes the possible loophole that a degree-two PC derivation could first derive new linear consequences and then multiply them: no such nonzero linear consequences exist after substitution.

Thus the original source system has no degree-two PC refutation.

4. A DEGREE-THREE UPPER BOUND FOR THIS PAIR OVER EVERY FIELD
For f(t)=t, the source and target nullities are a=2 and b=3, so a-b=-1 is nonzero over every field. The kernel-transport trace argument in KERNEL-TRANSPORT.md, with the sequential reuse refinement, gives a degree-three refutation: derive inverse intertwining with degree-three intermediates, derive the actual linear lower-left inverse block W=0, then reuse that line to obtain both quadratic inverse identities between the two unequal kernel spaces. Their rectangular traces give the nonzero constant a-b. No characteristic-zero assumption is required for this particular pair.

Equivalently apply the already proved sufficient kernel-nullity theorem only for this fixed nullity difference; no universal small-characteristic upper bound is asserted. Combining with Section 3 proves exact degree three.

5. PADDING
For n>4 use A_n=A directsum0_(n-4), B_n=B directsum0_(n-4). The nullity difference remains -1, so the same degree-three upper bound applies. For the lower bound, further substitute X_n=diag(X_4,I_(n-4)) and Y_n=diag(Y_4,I_(n-4)), with all off-diagonal blocks zero. The extra source equations become zero and the surviving system is exactly the four-dimensional one. Substitution by constants or linear polynomials preserves bounded PC degree, so a padded degree-two refutation would contradict Section 3.

6. EXACT CONTROL
conjugacy_sharpness_control.py constructs all 32 inverse-entry moment equations in 128 cross moments over Q and solves them exactly with Fraction Gaussian elimination. The system has rank 30 and returns precisely the six nonzero moments above; direct substitution checks every equation. This finite calculation verifies the explicit witness, while the line-span proof establishes the PC degree lower bound. The written integer moment identities establish the same witness in arbitrary characteristic.

ATTRIBUTION / SCOPE
Jordan blocks, kernel transport, rectangular trace and elementary PC rules are classical. The fixed matrices and explicit moment assignment are offered as an informal matching sharpness argument; publication priority is unverified. This is a positive exact-degree theorem combined with a matching upper bound, not a standalone lower-bound barrier. It concerns ordinary conjugacy with both inverse equations, not TI or a one-sided inverse encoding.
