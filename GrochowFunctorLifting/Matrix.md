# Mixed natural and nonsplit-quotient affine isometry in characteristic two

Status: informal proof; not Lean-certified; no publication-priority claim. This advances a sufficient case of the characteristic-two Matrix Tuple Isometry question, but does not close that published question in full.

## Exact published target and campaign outcome

Grochow, Qiao, Stange and Sun, On the complexity of isomorphism problems for tensors, groups, and polynomials V: over commutative rings, Section 1.4, state that polynomial-time Matrix Tuple Isometry over characteristic-two fields is still open. Given ordered tuples A_i,B_i, this asks whether one invertible P satisfies P transpose A_i P = B_i for every i. Their Section 5.3 solves the odd-characteristic local principal-ideal-ring version. The target here is the unrestricted characteristic-two field version; a sufficient adjoint-algebra case is not a full answer. [Original statement and context](https://arxiv.org/html/2611.00735v1).

Two routes were compared. Direct mixed-module affine equations initially involve a shared parabolic translation and a quadratic-refinement cocycle. Eliminating that translation with an anchor works for pure V/Ev modules, but leaves mixed top-coordinate equations. Reinterpreting those equations as full and restricted quadratic forms makes all remaining free lifts binary-linear. This route succeeds below. The second route would classify every invariant quotient of a parabolic natural isotypic module and then prove closure through arbitrary successive stabilizers. No such complete classification or closure theorem is established here. It is not used as an implicit oracle.

The two new sufficient results are: an exact polynomial geometric solver for simultaneous full and quotient vector markings with one full or partially specified quadratic form; and a polynomial affine transporter for arbitrary mixed copies of V and V/Ev under the actual one-vector symplectic stabilizer. They preserve the shared group element and actual isometry constraints.

## 1. A universal geometric lifting theorem for isotropic quotient markings

Let E be an explicitly presented finite field of characteristic two. Let V have a nondegenerate alternating bilinear form B. Let S be a specified totally polar-isotropic subspace, meaning B restricted to S is zero. Its dimension is arbitrary. We require the desired map g to lie in Sp(V,B) and fix S pointwise.

The input contains any number of full vector markings g f_i = f_i' and quotient markings

    g(w_j + S) = w_j' + S.

It may additionally contain one of the following:

- one full quadratic-form isometry Q_1(gx) = Q_0(x), where both polars are B;
- one partial quadratic-form isometry on H = S perpendicular, where the supplied Q_0,H and Q_1,H have polar B restricted to H.

There is a polynomial-time exact decision and witness algorithm in all these cases. No bound on the number of marks, dimension of S, field degree, or degeneracy of their combined span is imposed. The group remains the actual symplectic group fixing S; it is not replaced by a general-linear group or algebra-unit group.

### 1.1 The missing lift coefficients are linear variables

Choose a basis s_1,...,s_k of S. A quotient marking is equivalent to

    g w_j = w_j' + a_j, with a_j = sum_l alpha_{jl} s_l.

The alpha_{jl} are unknown E-elements. Since S is totally polar-isotropic, pairings of shifted target markings have no quadratic alpha-alpha term:

    B(w_i'+a_i,w_j'+a_j)
      = B(w_i',w_j') + B(a_i,w_j') + B(w_i',a_j).

Their pairings with full target marks and the fixed s_l are also E-linear in alpha. Impose agreement with all source B-pairings.

Compute the E-linear relations among the source classes of all full and quotient marks in V/S, and the corresponding target classes. Require that these relation spaces agree. This check is independent of alpha and ensures the eventual induced map on the quotient of the marked span by S is injective, not merely well defined. Then impose every actual linear relation among S and the source marks on the shifted target marks. These are E-linear equations in alpha.

After these tests, any solution defines an injective linear map on the source marked span, fixes S pointwise, and preserves B. Indeed any kernel vector projects to zero in V/S by the relation-space test, hence lies in S, and the map is the identity there. This injectivity check is essential for degenerate marked spans.

Without quadratic data, solve these linear equations and extend the resulting partial symplectic isometry by constructive Witt extension. Conversely every valid global g gives a solution, so this already proves the purely symplectic case.

### 1.2 Full quadratic data remains binary-linear

Assume Q_0 and Q_1 are supplied on all V, both with polar B. First require they agree on S and that their ambient Arf types agree. For a shifted quotient marking,

    Q_1(w_j'+a_j)
      = Q_1(w_j') + Q_1(a_j) + B(w_j',a_j).

Because B vanishes on S,

    Q_1(a_j) = sum_l alpha_{jl} squared times Q_1(s_l).

This is binary-linear in the alpha variables. Impose its equality with Q_0(w_j). The quadratic equalities on full marks are fixed tests. Together with the pairing and relation conditions, all equations are linear over F_2, including field squaring. A solution gives an injective partial quadratic isometry on the marked span. Ordinary Witt extension for the nondegenerate ambient polar constructs a global quadratic isometry. It necessarily preserves B and fixes S. This proves exact sufficiency and necessity for the full-quadratic case.

### 1.3 A partial quadratic form has only k extension parameters

Now suppose the quadratic data is specified only on H = S perpendicular. Require Q_0,H and Q_1,H to agree on S. Extend each arbitrarily to a quadratic form on V with polar B; do this by extending a basis of H and specifying its missing basis values. Fix the source extension Q_0. Every target extension is

    Q_1,delta(x) = Q_1(x) + sum_l delta_l B(s_l,x) squared.

These are exactly all extensions: two refinements with the same polar differ by the square of a linear functional, and vanishing on H puts that functional in the polar dual of S. There are k E-parameters delta_l.

For a quotient target lift w_j'+a_j, B(s_l,a_j) = 0, so the new extension terms do not multiply any alpha variable. The required quadratic equality is therefore

    sum_l alpha_{jl} squared Q_1(s_l)
      + B(w_j',a_j)
      + sum_l delta_l B(s_l,w_j') squared
      = Q_0(w_j) - Q_1(w_j').

It is binary-linear in alpha and delta. Full-vector quadratic equalities are linear in delta as well.

The remaining ambient-type condition is also binary-linear. For a refinement Q of nondegenerate polar B, adding B(z,-) squared changes its absolute Arf type by Trace_E/F2(Q(z)). Here z = sum_l sqrt(delta_l) s_l and B vanishes on S, so the type change is

    Trace_E/F2( sum_l delta_l Q_1(s_l) ).

Thus equality of the two ambient types adds one binary-linear equation, computed by field trace. This formula follows directly by extending the isotropic basis of S to a symplectic basis and using the ordinary Arf sum of paired basis values.

Solve the combined binary-linear system. Given a solution, the full-quadratic case and Witt extension construct g. Conversely if g fixes S and matches the partial quadratic data on H, then the transported source extension and target extension agree on H and differ by exactly the displayed k-parameter correction. The true g and its quotient-mark lifts therefore supply a solution. This proves exact equivalence.

### 1.4 Complexity and exact-output contract

There are polynomially many alpha and delta coordinates. Pairings, linear relations, field squaring, trace, and Arf computations use polynomial-size linear algebra over E or F_2. Constructive classical Witt completion is polynomial over the explicitly presented finite field; it permits a degenerate marked subspace because the ambient polar is nondegenerate. The output is an explicit g matrix. Direct substitution checks every full and quotient marking and the full or partial quadratic identity. No element of E^n or classical group is enumerated.

## 2. A polynomial affine solver for arbitrary mixed V and V/Ev modules

Let V be a symplectic E-space of dimension n at least 10, v a specified nonzero vector, P = Sp(V)_v its pointwise stabilizer, and N = V/Ev. Given genuine affine cocycles on

    V^r direct-sum N^s direct-sum T,

where T is any explicitly trivial binary module, arbitrary affine transport under the actual P-action is polynomial-time decidable and constructible. The integers r and s are arbitrary and may both be positive. This closes the mixed-module case deliberately excluded from the preceding Round3Matrix proof.

### 2.1 Exact cohomology inputs

The preceding explicit Q semidirect Sp(W) calculation proves that both H^1(P,V) and H^1(P,N) are one-dimensional over E. Their generators are the ambient quadratic-refinement cocycle and its projection. P is perfect, so the cocycle on T is zero. These are the exact group cohomology statements, not statements about the units of the spanned algebra.

For reference, choose w with B(v,w) = 1 and let W be their perpendicular complement. The unipotent group Q has maps

    n(u,t): v -> v,
            x -> x+B(u,x)v on W,
            w -> w+u+t v.

Its group law is (u,t)(u',t') = (u+u',t+t'+B(u,u')). It is elementary abelian in characteristic two. After killing the Levi cocycle, the central n(0,t) relations force the bottom component of a V-valued cocycle to vanish. Its middle component is lambda u and is removed by a lambda w coboundary. The remaining invariant Hom(Q,E) vanishes: write it A(t)+f(u), use Levi transitivity to make f constant on nonzero u, and use distinct perpendicular vectors to force that constant and then A to be zero.

For N the bottom component is directly an invariant Hom(Q,E), hence zero, and the same middle-coboundary argument applies. If Q_0(a v+x+b w)=a b+q_W(x), its refinement difference under n(u,t) is (t+q_W(u)) b squared. Its natural vector lies in Ev, so the projected N-cocycle vanishes on Q and restricts to the nontrivial refinement class on Sp(W).

The sole inherited non-elementary cohomology input is H^1(Sp(W),W) of dimension one in this safe rank. The full calculations and polynomial parameter extraction are recorded in the earlier Round3Matrix notes and use only actual cocycle evaluations on polynomial separating lists.

### 2.2 Geometric meaning of the two modules

Identify V with the space of zero-polar quadratic forms on V using polar duality and square roots of coefficients. This identification is binary-linear and P-equivariant; an E-scalar on the vector side becomes its square on the quadratic-form side, which is explicitly computed.

Restriction of these forms to H = v perpendicular has kernel exactly the Ev direction. Thus N identifies with zero-polar quadratic forms on H. Under these identifications, after absorbing a recovered coboundary into the source and target, each affine constraint becomes an isometry of either

    lambda_i Q_0 + L_i

on all V, or its restricted analogue on H, where L_i has zero polar. The polars of all nonzero-lambda forms are proportional to B or B restricted to H.

If a full-copy coefficient lambda_i is nonzero, retain its normalized full quadratic form. Subtract suitable multiples of it from every other full equation, and of its restriction from every restricted equation. All remaining forms have zero polar. Their square roots give full vector markings or quotient vector markings modulo Ev. Apply Theorem 1 with S = Ev and one full quadratic form.

If every full-copy coefficient is zero but some restricted-copy coefficient is nonzero, retain one normalized partial quadratic form on H. Subtract suitable multiples of it from the other partial equations. The full equations and all residual partial equations are zero-polar forms, giving full and quotient vector markings. Apply the partial-quadratic case of Theorem 1.

If every coefficient is zero, there is no quadratic-form constraint; apply its purely symplectic case. In every branch impose g v = v, and check equality of the trivial T-coordinates.

This constructs an actual g in P exactly when an affine transporter exists. The same g is used for every full and quotient coordinate. No separate choices of h, u, central parameter, or quotient matching are silently combined.

## 3. Consequence for an actual two-grade adjoint norm problem

In the characteristic-two norm-lifting setup, assume one simple symplectic residue block Sp(V), n at least 10. Permit arbitrary radical length but at most two nonzero graded Tate defects. Suppose the first active grade installs exactly one nonzero vector mark and no quadratic refinement, so its actual residue stabilizer is P = Sp(V)_v.

The second actual obstruction may now be any mixed V^r direct-sum (V/Ev)^s direct-sum T, with a supplied and checked P-module presentation. Apply Theorem 2 and the faithful physical preimage/radical correction routine. Later Tate defects vanish, so ordinary trace corrections finish all remaining grades. Thus this sufficient norm/isometry problem is polynomial, including mixed full and genuinely nonsplit quotient coordinates.

The theorem does not presume a presentation oracle. Any proposed presentation is checked on its explicit linear isomorphisms and a polynomial generating set of P. Concrete quotient patterns directly covered include disjoint original natural copies left unchanged, quotiented by their fixed Ev line, or quotiented by v perpendicular to give trivial coordinates. The earlier split-quotient construction supplies further full-V components. No claim is made that every P-invariant quotient has these types or that every abstract quotient occurs as an actual norm radical image.

Normalize the residue norm equation first by classical bilinear isometry. An actual residue matrix required for a cocycle evaluation is lifted through earlier grades by the fixed-residue unipotent algorithm; correctness of the maintained P image proves these calls succeed. At each accepted grade an actual algebra unit, not merely a residue label, is updated. Therefore the algorithm retains one consistent residue witness through all grades. Finite-algebra decomposition may be Las Vegas; the linear and geometric decisions are exact.

## 4. Scope against the unrestricted published question

The universal target is not closed. The proof still does not give a polynomial affine transporter for an arbitrary module quotient under an arbitrary iterated parabolic or marked orthogonal stabilizer. Nor does it prove that all adjoint algebras reduce to the stated one-vector, two-active-grade setting. A local linear solver or a ring-unit transporter is not a substitute for this missing actual-isometry statement.

The new positive advance is genuine: one exact geometric solver handles arbitrary isotropic-rank quotient markings and partial quadratic data; it implies the full affine mixed V plus V/Ev transporter for a point stabilizer, including the previously omitted genuinely nonsplit interaction. The higher-isotropic-rank geometric theorem is unconditional for its stated data, but no higher-flag cohomology normal form is assumed from it.

## 5. Sources, retrieval, and verification status

- Exact published frontier: Grochow–Qiao–Stange–Sun, Part V, Section 1.4, final paragraph, https://arxiv.org/html/2611.00735v1 . Section 5.3 gives the odd-characteristic tuple algorithm and adjoint-algebra framework.
- Natural symplectic cohomology: Kantor–Liebler, The rank 3 permutation representations of the finite classical groups, Theorem 2.14(i), https://pages.uoregon.edu/kantor/PAPERS/KantorLiebler.pdf . This table credits Pollatsek, Cline–Parshall–Scott, Jones and related work.
- Quadratic-refinement interpretation: Cherlin–Hrushovski, Finite Structures with Few Types, Fact 3.3.6, https://sites.math.rutgers.edu/~cherlin/Paper/2003FSFT.pdf .
- Physical unipotent lifting: Sun, Appendix A, Lemma A.24, https://arxiv.org/pdf/2611.05920 . Append a faithful regular 1+J representation tested at zero to the congruence representation, so no group kernel is lost.
- Constructive classical extension documentation: https://docs.magma-maths.org/v2.30-1/MatricesLinearAlgebra/PolarSpaces/isom-sim.html . The earlier Matrix notes spell out polynomial Witt completion with degenerate marked spans.

The current campaign reread the exact Part V frontier and its odd-characteristic scope. The targeted federated Lookup-DAG search for QuadraticForm Arf returned Axiom CFSG orthogonal-generation Arf material and the NoExoticSixSphere Arf invariant sources. Direct reads confirmed explicit standard quadratic coordinates in the former and an F_2 Gauss-sum/isometry invariant in the latter. These are source-only discovery records: the F_2 invariant is not an all-finite-field algorithm, and neither source is claimed as a new local kernel check or a proof of the present transporter. Earlier searches also found Mathlib group-cohomology infrastructure and external affine symplectic definitions. All proofs here are informal. The independent audit record is given at the end; no Lean verification or literature novelty check has been completed for the new assembly.


## 6. All point-stabilizer natural quotients over F_2

There is a further unconditional module classification when the residue center is exactly F_2. Let V, v and P be as in Section 2 over F_2. Every P-invariant quotient of V^r can be presented, in polynomial time, as

    V^a direct-sum (V/F_2 v)^b direct-sum F_2^c.

Consequently the actual P-affine transporter is polynomial for EVERY quotient of V^r, without a supplied-presentation promise. This is a theorem about the full quotient module family at this single stabilizer, not about arbitrary later stabilizers.

### Explicit classification and algorithm

Write V = F_2 v + W + F_2 w, using a symplectic partner w. On V^r use the common multiplicity space M = F_2^r and write

    V^r = A_top direct-sum (W tensor M) direct-sum B_bottom,

with A_top and B_bottom both identified with M. Let Z be a P-invariant subspace. Restriction to the Levi H = Sp(W) is a direct sum of the trivial module and copies of the simple natural W-module. Their types differ and End_H(W) = F_2. Therefore

    Z = T direct-sum (W tensor D),

where T is a subspace of A_top + B_bottom and D is a subspace of M. This uses semisimplicity of the particular restricted module, not a characteristic-zero assumption about the group algebra. Compute T and D by intersections and projections; for D one natural coordinate line suffices.

Set

    A_0 = {a in M: (a,0) is in T},
    B_0 = projection of T onto B_bottom.

The Q action forces B_0 contained in D and D contained in A_0. Indeed n(u,0) applied to a vector (a,0,b) in T changes its middle coordinate by u tensor b, forcing b into D. Applying n(u,0) to x tensor d in the middle changes the top coordinate by B(u,x)d, and a pairing value one forces d into A_0. The central top shift adds no new condition because B_0 is already contained in A_0.

The subspace T is the graph of a linear map f:B_0 -> M/A_0, together with A_0. Choose a linear lift of f and extend it to L:M -> M. The automorphism of V^r that adds L(b) to the top coordinate and leaves middle and bottom unchanged is P-equivariant: P fixes the top coordinates pointwise and fixes the bottom quotient. It is invertible because its added nilpotent map squares to zero. It turns T into A_0 direct-sum B_0 without changing D.

Now choose one basis of M adapted to the chain

    B_0 contained in D contained in A_0 contained in M.

The same change of multiplicity basis in every natural coordinate commutes with P. In each basis position the kernel and quotient are exactly:

- in B_0: the entire natural copy is in Z, so the quotient is zero;
- in D/B_0: the kernel is v perpendicular, so the quotient is trivial;
- in A_0/D: the kernel is F_2 v, so the quotient is N = V/F_2 v;
- outside A_0: the kernel is zero, so the quotient is V.

This supplies the claimed P-module decomposition by explicit Gaussian operations and P-equivariant changes of coordinates. Apply Section 2 to the resulting mixed module. Its cocycle is transported along the same checked module isomorphism, so no affine information is discarded.

### Strengthened norm corollary

In Section 3, if the residue center is F_2, the second actual obstruction quotient is automatically a quotient of V^r for the one-vector stabilizer P. The classification above computes its mixed presentation. Thus the polynomial two-active-grade norm theorem no longer needs the supplied/checkable mixed-presentation hypothesis in this binary-residue case. It permits an entirely arbitrary correction-image subspace at that second grade.

The structural assumptions that remain are one simple symplectic residue factor of center F_2 and dimension at least 10, at most two active Tate grades, and a first affine stabilizer equal to the point stabilizer of one nonzero vector with no installed quadratic refinement. These assumptions are checked from the actual graded construction. It is not claimed that all tuple-isometry inputs over F_2 have residue center F_2 or satisfy them.

Over a larger center E, the analogous top and bottom subspaces need only be binary-linear, while D is E-linear. One cannot silently adapt an E-basis to all of them. That larger-field classification is not proved by the preceding argument and is not included in this theorem.

### Independent audit record

A second worker independently checked the geometric partial-quadratic extension theorem, the mixed-module reduction, and this F_2 quotient classification. The audit found the injectivity test, Arf correction, Q-invariance flag conditions, shear, and quotient patterns valid. This is an informal independent audit, not a Lean kernel certificate or a literature priority finding.
