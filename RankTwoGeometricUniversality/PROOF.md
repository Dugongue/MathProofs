# Arithmetic and geometric universality at rank two

## Status and main statement

This is an informal strengthening of the binary rank-two completion construction. The new geometric argument has been checked by its author but has not received a separate worker review, external peer review, or Lean verification. Publication priority is unestablished. The earlier arithmetic gadgets have separate internal audits and finite checks.

**Theorem 1.** Let X be an affine scheme of finite type over Q, presented by finitely many polynomial equations. One can construct, in time polynomial in an arithmetic-circuit presentation of those equations and their rational coefficients, a partial matrix M with specified entries only 0 and 1 and a specified 2 by 2 identity block, such that its rank-at-most-two completion scheme C_M satisfies

\[
C_M\ \cong\ D(p)\ \subseteq\ X\times\mathbb A^k_{\mathbb Q}
\]

for some explicitly described polynomial p. Here D(p) means the open subset where p is invertible. The number k is polynomial in the input size; p can be represented by a polynomial-size arithmetic circuit. The projection C_M to X is smooth and surjective, and each fiber is a nonempty open subset of affine k-space. For every characteristic-zero field K and every x in X(K), that fiber has a K-point.

All completions have rank exactly two because of the identity block. The dimension of the matrix grows with the input; rank two does not mean a two by two input matrix. Every blank is independent. The theorem does not constrain completed entries or factors to be nonnegative.

Thus the construction preserves rational-point existence over every characteristic-zero field, preserves arbitrary singularities up to adjoining smooth variables, and, for integral X, preserves its stable birational class. This is substantially stronger than a reduction that only preserves a yes/no decision.

## 1. Keep the entire polynomial solution scheme

Clear rational denominators. Compile the defining equations into an arithmetic circuit with a variable for each intermediate value and equations for addition, multiplication, constants and final outputs zero. Eliminating a gate's output variable is a polynomial coordinate-ring isomorphism. Accordingly the gate solution scheme is isomorphic to X, including its possible nilpotent structure. No sum-of-squares replacement, Boolean encoding, or passage to a radical ideal is made in this step.

For each wire value x introduce a free parameter b_x and write

\[
x^- = b_x,\qquad x^+=x+b_x.
\]

Invert both values. Algebraically this replaces X by an open subset of X times affine space, with coordinate ring obtained by adjoining the b_x and inverting their products b_x(x+b_x). Every field-valued source point admits such choices because only two values for each b_x are forbidden.

The equations x+y=z and xy=z become, respectively,

\[
x^++y^++z^-=x^-+y^-+z^+,
\]

\[
x^+y^++x^-y^-+z^-=x^+y^-+x^-y^++z^+.
\]

All displayed summands are units after localization. For each equality introduce a fresh parameter s, start both sums at s, and require s and all partial sums to be invertible. Impose the additions successively and identify the two final values. Each side has at most three summands, so at most seven values of s are forbidden at any field-valued point. Each newly named product or partial sum is determined uniquely by the original wires, b parameters, and s parameters. Final equality gives exactly the original gate equation. Over a general Q-algebra the same identities hold with invertibility interpreted as being a unit.

Constants and zero outputs can be handled by the same method, or by identifying the two representatives of a zero wire and using x^-+1=x^+ for a one wire. Use a fresh split parameter for each original wire, retaining the equation that fixes its original constant value. Thus no source coordinate or relation is lost.

After eliminating determined variables, the resulting nonzero-scalar gate scheme has coordinate ring

\[
\bigl(\mathbb Q[X][b_1,\ldots,b_a,s_1,\ldots,s_b]\bigr)[p^{-1}],
\]

where p is the product of the values explicitly required to be units. The notation Q[X] denotes the coordinate ring of X; it is not assumed reduced. The product has a polynomial-size circuit. The free parameters, rather than the determined gate variables, are the k=a+b affine coordinates in the theorem.

## 2. An anchored matrix chart is a scheme chart

A matrix with a specified leading identity block has the form

\[
\begin{pmatrix}I_2&B\\ A&D\end{pmatrix}.
\]

Over any commutative Q-algebra, the equations given by all 3 by 3 minors are equivalent, as ideals, to the entrywise equations D=AB. Each entry of D-AB is a 3 by 3 minor using the anchor rows and columns. Conversely D=AB factors the full matrix as the product of an m by 2 matrix and a 2 by n matrix, so every 3 by 3 minor vanishes.

Consequently the completion scheme is precisely the scheme of row and column vectors in two coordinates, with the anchor vectors fixed to the standard basis and prescribed pairings equal to 0 or 1. This is a coordinate-ring identity, not merely a field-valued rank argument.

## 3. Scalar gadgets preserve coordinate rings

Fixed rows and columns (1,1), (1,-1), (-1,1) and signed axes can be forced with 0/1 pairings. For example pin the first coordinate of a vector to 1 and its pairing with (1,1) to 0 to force (1,-1). A first coordinate equal to -1 is forced by pairing with the fixed negative first axis to give 1. These steps involve only elimination with unit coefficients.

For a scalar label x use a row R=(x,1). Add the following auxiliary vectors with the indicated equations and pinned zero coordinates:

| Auxiliary | Equations |
| --- | --- |
| Column U=(u,0) | R U=1 |
| Row D=(d_1,d_2) | D(1,-1)=0; D U=1 |
| Column V=(0,v) | D V=1 |
| Column K=(-1,h) | R K=0 |
| Row Q=(0,w) | Q K=1 |
| Column L=(l_1,l_2) | (1,-1)L=0; Q L=1 |
| Row P=(t,0) | P L=1 |

These equations force x to be a unit and force, uniquely,

\[
U=(x^{-1},0),\quad D=(x,x),\quad V=(0,x^{-1}),\quad
K=(-1,x),\quad Q=(0,x^{-1}),\quad L=(x,x),\quad P=(x^{-1},0).
\]

The identities are valid over every commutative Q-algebra, including algebras with nilpotents. A fresh row coordinate is forced to x by unit pairing with U or V. A fresh column coordinate is forced to x by unit pairing with P or Q. No coordinate-copy step introduces a free parameter.

Multiplication xy=z is imposed by a fresh row (x,z) and column (y,-1) with pairing zero. Addition x+y=z is imposed by auxiliary units u,v with uz=x, vz=y, and u+v=1. Since z is a unit, u and v are uniquely x/z and y/z. All remaining gadget coordinates are likewise forced. Hence the matrix construction is isomorphic to the nonzero-scalar gate scheme, not just equisatisfiable with it. Fresh rows and columns keep distinct constraints at distinct matrix positions. The remaining blank entries are forced by D=AB; they contribute no further freedom.

Combining Sections 1–3 proves the displayed isomorphism C_M isomorphic to D(p). Its explicit construction has polynomially many vectors and therefore polynomially many matrix entries.

## 4. Geometry and field-valued fibers

Projection from X times affine k-space to X is smooth, and restriction to an open subset remains smooth. At a point with residue field K, choose each split parameter to avoid zero and the negative of its wire value, then each shift parameter to avoid the finitely many forbidden partial sums. Every characteristic-zero field is infinite, so this always succeeds. The same applies over algebraic closures. Thus all fibers are nonempty opens in affine k-space, and the projection is surjective.

If X is geometrically integral, so is C_M. If X is smooth over Q, so is C_M. For any field extension K/Q and x in X(K), choose a lift y in C_M(K). Since D(p) is an open subset of a product and p(y) is nonzero, the completed local rings after base change to K satisfy

\[
\widehat{\mathcal O}_{(C_M)_K,y}\cong
\widehat{\mathcal O}_{X_K,x}[[t_1,\ldots,t_k]].
\]

This describes preservation of singularities up to smooth variables. No assertion of identical topology, contractible real fibers, or a bijection of point sets is made. If X is integral, its product with affine k-space and C_M have the same function field, proving the stable birational assertion.

## 5. Locally solvable completion is still arithmetically universal

**Corollary 2.** Rational polynomial solvability reduces in polynomial time to binary rank-two matrix completion restricted to instances admitting rank-two completions over R and over every Q_p. This is an unconditional equivalence of decision problems on the promised family.

Given equations f_i=0, put f=sum_i f_i^2 and

\[
H(u)=(u^2-13)(u^2-17)(u^2-221),\qquad F=fH.
\]

Since H has no rational root, F has a rational zero exactly when all f_i do. H has a root over every completion of Q. For odd primes other than 13 and 17, either 13 or 17 is a square unit, or their product is; Hensel lifting supplies the root. At 13 use 17, at 17 use 13, and at 2 use 17, which is 1 modulo 8. Over R use 13. Apply Theorem 1 to F=0. Its field-point surjectivity preserves the required local points. The reverse decision reduction expresses the anchored rank-two equations over Q.

This uses the explicit local-witness polynomial already appearing in the project's rational unit-distance work. It does not require a claimed undecidability theorem as a premise.

## 6. Even smooth geometrically integral completion spaces

**Corollary 3.** Rational polynomial solvability is computably many-one equivalent to binary anchored rank-two completion with the simultaneous promises that its completion scheme is smooth and geometrically integral over Q and that it has a point over R and every Q_p. No polynomial-time bound is claimed for the smoothing step.

Here are the details of the smoothing construction, adapted from the project's smooth rational-point reduction. Start with F=fH above and compile its vanishing into quadratic gate equations q_j=0. Set G=sum_j q_j^2+v^2 using a fresh variable v. Then G is nonconstant; over Q its zeros recover exactly the original solutions. At every completion there is a point where all q_j and v vanish.

The elliptic curve y^2=z^3+z has only the affine rational point (0,0). For z=a/b>0 in lowest terms, rational squareness forces ab(a^2+b^2) to be a square integer. Pairwise coprimality makes a,b,a^2+b^2 squares, giving a nonzero solution of A^4+B^4=C^2, excluded by Fermat's classical descent. Negative z gives a negative right side, and z=0 gives y=0.

For a nonzero rational integer c consider

\[
S_c\colon\quad z^3+z=c^2G^2.
\]

Its rational points therefore have z=0 and G=0, and conversely every rational zero of G lifts. The local points chosen above also lift with z=0 for every c.

This hypersurface is geometrically integral. Otherwise the monic cubic in z has a root in the geometric rational function field of the variables of G. That root, together with cG, gives a nonconstant rational map from affine space to the elliptic curve. Restricting to a suitable line and extending to the projective line contradicts Riemann–Hurwitz.

Only finitely many nonzero c give a singular hypersurface. A singular point satisfies 3z^2+1=0, G nonzero, and every partial derivative of G equal to zero. A polynomial in characteristic zero has finitely many critical values: on each irreducible component of its critical locus the differential is zero, so its value is constant. These finitely many nonzero values, together with the two possible z values, exclude only finitely many c. Enumerate nonzero integers c and test the Jacobian ideal for the unit ideal, stopping at a smooth choice. This is effective, without an asserted polynomial-time bound.

Apply Theorem 1 to this smooth geometrically integral S_c. The resulting completion scheme is smooth and geometrically integral, has points over all the completions, and has a rational point exactly when the original rational equations are solvable. The reverse reduction is again immediate from the matrix equations.

## 7. Conditional undecidability and exact limits

If Hilbert's tenth problem over Q has a negative answer, Corollary 3 makes rational rank-two completion undecidable even with all its smoothness and local-solvability promises. If one additionally assumes a Diophantine definition of Z in Q, the usual MRDP reduction makes the promised family halting-hard and computably enumerable, hence halting-complete. Neither arithmetic premise is proved in this document.

Under undecidability there can be no total computable uniform bound on the numerator and denominator sizes of rational completions for promised yes-instances. Such a bound would allow finite exhaustive search and decide the promised problem. This is an exact rational-witness statement, not a claim that all approximate numerical methods fail.

For the real completion problem the unconditional existential-real hardness remains. For fixed finite fields the separate projective-coloring reduction proves NP-completeness. These conclusions do not prove P versus NP, VP versus VNP, or special-linear tensor-isomorphism containment. In particular, meeting a coordinate affine section of a rank orbit is a different problem from comparing two fully supplied tensor orbits.

## Attribution, novelty and significance

The immediate ingredients are the project's binary rank-two arithmetic construction, its rational-point smoothing construction, and its local-witness polynomial. The rest is explicit coordinate-ring elimination and standard geometry of affine space and open immersions. The unrelated tensor-isomorphism equivalences are not needed for this theorem and are not treated as interchangeable with completion.

Universality in matrix problems is an established subject. [Shitov's tensor-rank work](https://arxiv.org/abs/1611.01559) already gives general matrix-completion completeness at rank three, and [his nonnegative-factorization universality theorem](https://arxiv.org/abs/1606.09068) realizes general semialgebraic spaces in a different matrix model. The proposed contribution here is the simultaneous ordinary rank-two, binary-entry and scheme-level statement, together with its smooth locally solvable arithmetic consequence. The literature search has not certified priority for this exact combination.

Project antecedents: [rank-two completion](https://github.com/Dugongue/MathProofs/tree/main/RankTwoAndRingUniversality), [smooth rational-point decision](https://github.com/Dugongue/MathProofs/tree/main/RationalPointDecision), and [rational unit-distance local witnesses](https://github.com/Dugongue/MathProofs/tree/main/RationalUnitDistance). The first may still be a staged rather than published dependency; Sections 1–3 above supply the needed gadgets in this document.

If the proof and novelty survive specialist scrutiny, this is a plausible substantial paper joining arithmetic geometry, realization-space universality, and exact low-rank feasibility. The evidence does not justify predicting major prizes or broad acclaim. It is not a solution to an established grand conjecture merely because it has several consequences.
