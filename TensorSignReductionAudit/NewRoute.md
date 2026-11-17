# Finite-group and orientation-cover attack on the one-sign reduction

Status: informal research audit; no unrestricted reduction proved. This file is an attempt record, not a new open-problem closure or a theorem asserted to establish the requested reduction.

## Fixed target

Over F_3, let B(T,S) ask for a transporter with determinant one in two specified modes, and let A ask for one specified determinant. The unchanged target is a deterministic polynomial-time construction of one A instance equivalent to B(T,S), with no supplied transporter, stabilizer generators, flags, or orientation certificates.

The earlier conjunction packet already proves useful sufficient cases and proves that a common object-map conjunction would imply the stronger ordinary TI endpoint collapse. The present search did not remove those qualifications.

## 1. Finite-group/Frobenius route

The attractive construction is a truncated homogeneous algebra with relations x_i^3=t^2 x_i. In characteristic three, preserving these relations can force the induced degree-one maps, after a common scalar, to have entries in F_3. The earlier cubic norm construction exploits exactly this phenomenon with polynomially many low-degree monomials.

This does not select SL_n(F_3) inside GL_n(F_3). Both determinant signs satisfy the entrywise Frobenius equations. Adding a one-dimensional variable labeled as a determinant line without a relation proving its transformation law permits an independent scalar on that line. It therefore does not enforce the missing sign.

A genuine use of this route would need a further explicit polynomial-size algebra relation whose actual automorphisms induce precisely the desired determinant kernel. No such relation was established here. In particular, the fact that the determinant is a one-dimensional representation is not a construction tying that representation to the original module.

## 2. Small determinant circuits and unitriangular factorizations

The determinant has polynomial-size arithmetic circuits; matrices of determinant one have short elementary-matrix factorizations. These facts do not by themselves compile to a tensor-isomorphism instance.

The exact issue in the proposed gate encoding is visible already in Z=XY. With coordinatewise multiplication on triples, the set {(X,Y,Z): Z=XY} is not a subgroup for noncommuting matrices. For example, (X,I,X) and (I,Y,Y) satisfy the relation, whereas their product in the opposite order is (X,Y,YX), which fails it whenever XY differs from YX. Tensor automorphisms form a subgroup, and their images on invariant subquotients remain groups. Thus a construction claiming to realize these gate variables as independent invariant change-of-basis blocks must supply a different group-compatible multiplication law; the literal gate encoding is invalid.

This observation does not rule out a pair-dependent many-one construction. It identifies the missing proof in this particular attempted circuit transfer. A polynomial verifier or succinct factorization is not the requested one-instance reduction.

## 3. Finite orientation covers and permutation actions

A determinant sign can be represented through the action of GL_n(F_3) on the nonzero vectors, followed by the permutation sign. The action on all vectors is faithful and its permutation sign equals det(g): elementary transvections have odd-order cycles and hence even sign; diag(-1,1,...,1) exchanges 3^(n-1) pairs and therefore has negative sign. For n >= 1 these elements generate GL_n(F_3), proving the equality for every matrix; n = 0 is trivial. An independent exhaustive control checked every invertible matrix in dimensions 1, 2, and 3: respectively 2, 48, and 11,232 matrices, with zero sign mismatches. For n = 1 the nonidentity map exchanges the two nonzero vectors, exactly as required. These finite controls are not a replacement for the general generator proof.

This representation uses 3^n-1 points. An explicit permutation or incidence gadget formed from it has exponential size in the mode dimension, and dense tensor inputs of dimension n^3 do not pay for that expansion. I did not find a polynomial-size replacement which preserves the action for all transporters. Passing only to a selection of vectors requires proving that selection is intrinsic and that all relevant maps extend; that is not available for arbitrary tensors.

This exact determinant-reading identity is classical in substance and is not claimed as a new result. It gives an explicit all-input construction with the wrong size, rather than an unproved polynomial one.

## 4. Double covers, spinor norms, and local algebra

Classical double covers and determinant lines supply honest orientation objects. However an abstract cover of an acting group does not specify a polynomial-size tensor representation whose isomorphisms lift exactly the original relative transporters. Spinor constructions may require modules exponential in the rank. Adjoint representations or conjugation on matrix algebras are polynomial-size but often erase precisely the central determinant character one is trying to retain.

The existing determinant-neutral matrix-algebra amplification remains valid as a way to absorb ordinary TI conjuncts. It does not change an independent signed conjunct into an ordinary one. No added use of the cover route removed that condition.

## Search provenance and scope

Federated source/notes searches used the workspace lookup front door for orientation double covers, Dickson/determinant structure, Pfaffian determinants, and alternating/parity isomorphism. Relevant hits included source-only orientation-cover records, top-exterior determinant formulas, existing Pfaffian calibration notes, and the earlier TI/SL-TI research notes. Source catalog hits were treated as discovery records, not fresh kernel verification. The targeted searches do not constitute a proof that every library or every possible route was exhausted.

Primary literature checked:

- Chen, Grochow, Qiao, Tang, Zhang, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials III: Actions by Classical Groups*, https://arxiv.org/abs/2306.03135 . The tensor-system compiler handles an explicitly given bounded-order system; it does not establish that arbitrary arithmetic-circuit predicates on transporters are such a system.
- Grochow and Qiao, *On the Complexity of Isomorphism Problems for Tensors, Groups, and Polynomials I: Tensor Isomorphism-Completeness*, https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full . Algebra encodings preserve their stated isomorphism problems; no automatic determinant-kernel extension follows.
- Fortnow and Grochow, *Complexity Classes of Equivalence Problems Revisited*, https://arxiv.org/abs/0907.4775 , and Finkelstein and Hescott, *Polynomial-time kernel reductions*, https://arxiv.org/abs/1604.08558 . These clarify the distinction between object maps and arbitrary many-one reductions used in the previous packet.

Outcome: no sufficient unrestricted construction was found in this route. The all-input determinant permutation representation is explicit but exponential; the polynomial Frobenius and adjoint constructions do not yet enforce the required second sign. The earlier exact restricted reductions remain the positive results, with their restrictions unchanged.
