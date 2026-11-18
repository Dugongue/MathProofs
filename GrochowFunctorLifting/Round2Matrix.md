# Repeated characteristic-two lifting through nondegenerate markings

Status: informal sufficient theorem, not Lean-certified and not an unrestricted solution. Publication priority has not been established. This builds on the exact graded Tate decomposition, physical unipotent lifting, and full symplectic affine solver in OriginalMatrix.md.

## Exact sufficient theorem

Let A be an explicitly presented finite-dimensional algebra over a finite field of characteristic two, with involution *, Jacobson radical J, and self-adjoint unit c. Suppose A/J is one simple matrix algebra with first-kind symplectic adjoint involution. Write its residue unitary group as Sp(V), where V has even E-dimension n over its center E. Assume n is at least 8.

There is a polynomial-time lifting algorithm allowing this same residue factor to appear at arbitrarily many radical grades. Its sufficient promise is the following completely explicit condition on its extracted markings: at every successful nonterminal grade, the new target marking span in the currently moving space is nondegenerate for its polar form, and its orthogonal complement either is zero or has dimension at least 8. The extraction is defined below by linear equations and classical cohomology normal forms. The algorithm tests this condition. It returns either a norm witness, a valid rejection, or OUTSIDE_SCOPE when this regularity condition fails. On every input satisfying the condition it decides and constructs a norm witness in Las Vegas polynomial time. A zero marking span is permitted. A mark spanning the entire moving space is terminal and permitted.

The corresponding ordered matrix-tuple isometry instances have the same guarantee under their usual adjoint norm reduction. No bound on radical length, radical dimension, marking multiplicities, field extension degree, or the number of revisits is imposed.

The condition is a sufficient structural condition on the successive actual affine obstruction modules. It is not asserted for every raw tensor or tuple. It does not assume an unknown gadget, subgroup solver, or oracle.

## 1. Exact group models retained through all grades

Keep one actual accumulated norm transporter. Maintain a polar orthogonal decomposition V = U perpendicular R, where U is fixed pointwise by the current residue stabilizer. Its action on R is one of:

1. the full symplectic group Sp(R);
2. the full orthogonal group O(Q_R), for a stored quadratic refinement Q_R of the polar form;
3. Omega(Q_R), the kernel of the Dickson invariant in O(Q_R).

Before starting the grades, solve the residue norm equation by classical bilinear isometry. If it fails, reject. Otherwise lift a residue solution a, replace c by (a*) inverse times c times a inverse, and now c = 1 modulo J. A normalized witness w gives w a for the original norm equation. Initially U = 0, R = V and the group is Sp(V). Every nonzero R used below has dimension at least 8. If R = 0, the residue group is trivial, and the existing fixed-residue unipotent algorithm finishes all remaining grades directly.

A group element in one of these models is explicitly embedded in A/J as the identity on U and its given classical matrix on R. At a radical grade k the actual congruence-stabilizer image is exactly the maintained group. Given any required residue element, its physical preimage through the previous grades is computed by the fixed-residue unipotent routine. The mathematical invariant proves those calls succeed. This is not an assumed preimage oracle.

## 2. The obstruction module under a marked residual group

The universal Peirce/Frobenius/matrix-unit calculation gives each T_k as a sum of squared dual natural modules of the original Sp(V). Normalize its Frobenius coordinates over the binary field. On restriction to the current residual group, each copy splits as

    U_trivial direct-sum R_natural.

For a residual Sp, O or Omega of dimension at least 8, the natural binary representation is simple with endomorphism field E and has no fixed vector. For O and Omega these are the usual natural-module facts for finite classical groups, including the binary field; the dimension bound removes small reducible cases. Thus T_k is a semisimple binary module consisting only of trivial modules and natural copies. In particular an invariant binary subspace is a direct sum of its intersections with those two isotypic pieces. This is semisimplicity of this particular module, not Maschke's theorem for the characteristic-two group algebra.

The radical correction image contains the trace image. Therefore the remaining obstruction W_k is a quotient of T_k and has the same explicit form

    W_0 direct-sum R^r,

where the group acts trivially on the binary space W_0 and naturally on the E-space copies R^r. No arbitrary module extension is introduced in this nondegenerate splitting.

This quotient presentation is computable without searching the classical group. First intersect the known binary subspace with the two explicit summands. In the natural isotypic part R^t, every submodule has the form R tensor_E D for a multiplicity subspace D of E^t. Recover D by intersection with a fixed coordinate line of R, then take an E-linear complement in the multiplicity space. The trivial part uses ordinary binary quotient bases. Equivalent Hom/retraction linear systems on a known elementary classical generating set also compute the presentation. All matrices have polynomial dimensions.

## 3. Cohomology normal forms are explicit linear algebra

The graded physical lifts give a genuine right cocycle d: C -> W_k. Its evaluation on any prescribed polynomial list of residue matrices is obtained by actual lifting and reduction modulo J^{k+1}.

For a full symplectic residual group, its natural-module H^1 is one-dimensional over E, generated by the quadratic-refinement cocycle kappa(g) = Q_0 composed with g minus Q_0. Hence

    d_N(g) = z^g - z + lambda kappa(g),

coordinatewise, with one scalar lambda_j per copy and z in R^r. Its trivial part is zero, since the symplectic group is perfect in this rank range.

For Omega in even characteristic and dimension at least 8, natural-module H^1 is zero. This is exactly the zero case in Kantor–Liebler Theorem 2.14(i); the exceptional Omega^+_6(2) and odd-dimensional exceptions are outside the guard. For O, use the normal subgroup Omega of index two. The natural Omega-fixed space is zero and H^1(Omega,R) = 0, so inflation–restriction gives H^1(O,R) = 0. Consequently in both orthogonal cases

    d_N(g) = z^g - z.

The groups Omega are perfect in this rank range. Thus d_0 = 0 on Omega. For O, its abelianization is the Dickson quotient of order two, so

    d_0(g) = Dickson(g) t

for a binary vector t in W_0.

The parameters z, lambda and t are recovered by linear equations from genuine cocycle evaluations. In the orthogonal case one can avoid a hidden generation algorithm: choose a spanning list of nonsingular vectors v_i in R, and let s_i be their orthogonal symmetries. Each s_i has Dickson invariant one, and the products s_i s_j belong to Omega. Their common fixed space is zero: a vector fixed by all such products has all s_i-images equal; two independent symmetry directions then force that common image to be the vector itself, and spanning directions force the vector to be zero. Thus the equations on these products uniquely recover z. Evaluate one symmetry to obtain t when C is O. Since a global normal form exists by H^1 vanishing, its unique solution on the separating list is the global one.

For the symplectic case, use a polynomial separating set, not an incorrectly small purported generating set. Fix a symplectic basis e_i,f_i and the hyperbolic refinement Q_0. Represent the natural module as zero-polar quadratic forms. For a transvection T_v(a), the coboundary of z has coefficient a squared times z(v) along B(-,v) squared, while kappa has coefficient a squared times Q_0(v) plus a. In a homogeneous fit, division by a squared gives z(v) + lambda (Q_0(v) + a inverse) = 0. If E has more than two elements, take v among the basis directions and take a = 1 and one binary basis element outside the prime field. Their distinct inverses force lambda = 0, after which the basis directions force z = 0. If E = F_2, take the basis directions and e_1 + e_2, with a = 1. The three directions e_1, e_2, e_1 + e_2 have Q_0-value zero; additivity of the zero-polar z makes lambda nonzero impossible. Again the basis directions force z = 0. Thus the evaluation equations have a unique solution; the global cohomology normal form guarantees existence, so this is the global solution. No enumeration of E^n or Sp(R), no primitive multiplicative generator and no discrete logarithm is used.

## 4. Solve the actual affine transporter and update its exact stabilizer

The graded norm equation is e^g + d(g) = 0, with e the actual current source defect. The following solves it and computes the exact residue stabilizer of the target zero.

### Symplectic phase

If lambda = 0, require e_0 = 0 and match the vectors e_N + z to z under Sp(R). The exact target stabilizer fixes the span S of the target vectors z. Test that S is polar-nondegenerate and that R' = S perpendicular in R is zero or has dimension at least 8. Witt extension constructs the transporter if and only if the marked partial symplectic isometry is valid. The next group is Sp(R'), acting identically on U direct-sum S.

If some lambda_j is nonzero, divide that coordinate by lambda_j. It supplies one source quadratic form and one target quadratic form with the same nondegenerate polar form. Subtract suitable scalar multiples of this coordinate from every other coordinate; all remainders have zero polar and become vector markings after square roots and polar duality. Let Q be the target quadratic form and S the span of the resulting target marks. Test the same nondegeneracy and residual-rank condition on S. Ordinary quadratic isometry with these marks constructs the transporter exactly when ambient types and the marked partial quadratic isometry agree. The exact target stabilizer is O(Q restricted to R'), with U direct-sum S fixed pointwise. This installs the stored quadratic refinement for the orthogonal phase.

When lambda is zero, the marking span is the image of z in the natural factor. When lambda is nonzero, it is generated by the zero-polar remainders z_i minus (lambda_i/lambda_j) z_j. Changing the chosen nonzero coordinate only changes their generating list. Thus the condition is not a guessed list of desirable marks.

### Orthogonal phase

Require that the trivial-part equation is consistent. On Omega this means e_0 = 0. On O, if t = 0 again require e_0 = 0; if t is nonzero, e_0 must be either zero or t, prescribing Dickson(g) as zero or one respectively.

The natural part asks for simultaneous matching e_N + z -> z under the stored orthogonal form Q_R. Let S be the target marking span, and test that it is polar-nondegenerate with residual complement R' either zero or of dimension at least 8. Construct one marked quadratic isometry by Witt extension.

If membership in Omega or the trivial-part equation prescribes its Dickson bit, adjust the obtained isometry by an orthogonal symmetry supported on R' whenever necessary. Every nonzero allowed R' is a nondegenerate quadratic space of dimension at least 8 and contains a nonsingular vector; its symmetry fixes all target marks and has Dickson bit one. If R' = 0, the marked map determines the entire residue matrix, so simply test its Dickson bit. Thus the required parity is enforced without branching over group elements.

The target stabilizer is full O(Q_R restricted to R') if the previous group was O and t = 0. It is Omega(Q_R restricted to R') if the previous group was Omega, or if t is nonzero. This follows because fixing the natural obstruction means fixing z, while fixing the trivial obstruction means lying in the kernel of the Dickson character when that character is present. The new fixed space is U direct-sum S.

## 5. Physical correction, completeness and running time

At every success lift the chosen residue matrix through all previous grades, then solve the prescribed radical-image equation to cancel the residual error at the current grade. This updates one actual algebra unit. Preserve the new classical-group model as the exact residue image of the target congruence stabilizer. The following grade uses this same image and its physical preimages. A residue choice is never replaced by an unrelated solution.

Each affine test is exact for the maintained group, and the radical image includes every identity-residue adjustment. Therefore any rejection is a genuine rejection, not merely failure of the chosen presentation. If a nondegeneracy or residual-rank guard fails, report OUTSIDE_SCOPE rather than rejecting the mathematical instance. If the guard holds throughout, induction proves completeness: the image model is preserved, each successful transporter is extended physically, and after at most dim A grades the exact norm identity is obtained. Reaching a zero moving space invokes the already polynomial fixed-residue solver for all remaining grades.

There are polynomially many grades, algebra products, classical partial-isometry operations, cocycle evaluations, and binary or field-linear systems. The classical spaces and all regular/congruence representations have polynomial dimensions. Finite-algebra decomposition may use Las Vegas algorithms; all represented identities are exact. This proves the claimed sufficient polynomial-time bound.

## 6. Why this goes beyond the preceding result

The earlier theorem forbids a residue block from appearing at two different obstruction grades. This theorem explicitly permits arbitrarily many revisits to the same large block, retains a full residual classical group after each nondegenerate marking, and handles its Dickson character exactly. Neither a square-zero radical, a stable algebra section, nor an enumeration of the semisimple unit group is required.

The proof does not handle a degenerate new marking span or an unresolved residual group of dimension 2, 4 or 6. It also does not assert a general simultaneous parity-code theorem for several orthogonal residue factors. Those are outside this exact statement. In particular it does not close unrestricted characteristic-two tuple isometry or TI versus SL-TI.

## Primary sources and exact inherited inputs

- Kantor–Liebler, The rank 3 permutation representations of the finite classical groups, Transactions AMS 271 (1982), Theorem 2.14, PDF page 8: https://pages.uoregon.edu/kantor/PAPERS/KantorLiebler.pdf . This records natural-module H^1 dimensions and exceptions. The symplectic case has dimension one; the even-dimensional orthogonal Omega cases used here have dimension zero.
- The same paper, Section 2A, defines the classical natural groups and the finite-field geometric setting; its references credit Pollatsek, Cline–Parshall–Scott and Jones for the cohomology calculation.
- Cherlin–Hrushovski, Finite Structures with Few Types, Fact 3.3.6: https://sites.math.rutgers.edu/~cherlin/Paper/2003FSFT.pdf . Supplies the interpretation of the nontrivial symplectic affine class as a quadratic refinement.
- Sun, Appendix A, Lemma A.24: https://arxiv.org/pdf/2611.05920 . Supplies the unipotent affine transporter. Use a faithful regular 1 + J summand tested at zero, in addition to congruence, so all physical kernel elements remain represented.
- The classical constructive Witt extension steps are described explicitly in OriginalMatrix.md; implementation documentation: https://docs.magma-maths.org/v2.30-1/MatricesLinearAlgebra/PolarSpaces/isom-sim.html . Degenerate marked spans are allowed in that underlying extension theorem, but the new sufficient closure condition intentionally requires nondegeneracy to keep the next residue model exact.
- Published question and unrestricted scope: Grochow–Qiao–Stange–Sun, Part V, Section 1.4, https://arxiv.org/html/2611.00735v1 . This document is a sufficient-case advance only.


## Audit supplement: binary natural modules of the orthogonal groups

For completeness, the irreducibility and endomorphism facts in Section 2 can be proved directly, without treating E-linearity of a binary subspace as an assumption. Let Q have nondegenerate polar B, dimension n at least 8, and let Omega be the Dickson kernel in O(Q).

Omega is transitive on each nonzero quadratic-value level, including the nonzero singular vectors. Witt extension first gives an O(Q)-map between two vectors of the same quadratic value. If its Dickson bit is wrong, multiply by a nonsingular symmetry fixing the target vector. Such a symmetry exists because the target perpendicular hyperplane has dimension n - 1, larger than the maximal totally singular dimension n/2. Thus the hyperplane contains a nonsingular vector.

Let X be a nonzero binary Omega-invariant subspace. If X contains a nonsingular v, intersect a maximal totally singular space with v perpendicular; since its Witt index is at least 3, the intersection contains a nonzero singular u. The vectors v and v + u have the same nonzero Q-value. Transitivity gives v + u in X, hence u in X. If the original nonzero vector was singular no preliminary step is needed. Transitivity now puts every nonzero singular vector in X. These span V over F_2: all hyperbolic directions and their E-multiples are singular; any vector w in the anisotropic complement is the sum

    (w + e + Q(w) f) + e + Q(w) f,

of singular vectors, using one hyperbolic pair e,f. Hence X = V. This proves binary simplicity for Omega and therefore for O.

For the endomorphism ring, fix a nonzero singular e. The common fixed space of its Omega point stabilizer is exactly E e. Indeed, for x outside E e choose a nonsingular w in e perpendicular with B(x,w) nonzero. Such a w exists because nonsingular vectors span e perpendicular: a singular vector y in that hyperplane is the sum of two nonsingular vectors by choosing a nonsingular z in e perpendicular intersect y perpendicular; that intersection has dimension at least n - 2 greater than n/2. Also choose a nonsingular z in e perpendicular intersect x perpendicular. The product of the symmetries in w and z lies in Omega, fixes e, and moves x. Thus x is not fixed by the point stabilizer.

A binary endomorphism commuting with Omega therefore sends e to a e for one a in E. Transitivity on singular vectors shows it acts by this same scalar a on every singular vector. Their binary span is V, so the endomorphism is multiplication by a. Consequently End_{F_2 Omega}(V) = E, and the same holds for O. This justifies the multiplicity-space quotient extraction used in Section 2.

Spanning nonsingular directions used to recover orthogonal coboundaries can also be constructed by polynomial linear algebra. For a singular basis vector y, choose a nonsingular v in y perpendicular; the restriction of Q there has nonzero polar part in this dimension, so a basis vector or a sum of two basis vectors has nonzero value. Then v and v + y are nonsingular and sum to y. Applying this to the basis gives a polynomial-size nonsingular spanning list.

For the Dickson invariant and the explicit symmetry formula, see Nebe and Parker, Equivariant quadratic forms in characteristic 2, Section 3: https://www.math.rwth-aachen.de/~Gabriele.Nebe/papers/witt2.pdf . It defines the invariant by rank(g - 1) modulo two and cites Taylor, Theorem 11.43. The symmetry in a nonsingular v is x -> x + B(x,v) v / Q(v); it has rank(g - 1) = 1. All parity adjustments in this proof are therefore explicit matrix operations.
