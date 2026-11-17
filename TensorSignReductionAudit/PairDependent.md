# Pair-dependent conjunction audit: multiplication networks and unitriangular layers

Status: informal internal audit, not an unrestricted reduction and not a publication claim. The target is two-sign tensor isomorphism over F3 reducing deterministically in polynomial time to one one-sign instance. This audit investigated paired block swaps, shared transporter circuits, and multiplication-tensor representations of four unitriangular layers. No complete compiler was obtained.

## Exact multiplication-tensor calculation

For matrix multiplication X Y = Z, the usual simultaneous changes of bases have the form

    X -> A X B^-1,    Y -> B Y C^-1,    Z -> A Z C^-1.

Thus the relative matrices A B^-1, B C^-1, A C^-1 obey the desired telescoping product. This identity alone is insufficient: these relative matrices are values of the mode transformations at the identity matrix, not independent representation coordinates on which arbitrary fixed tensor stabilizers can impose subgroup membership.

Here is the exact outcome of the natural affine-slice construction. Let U be the full upper unitriangular subgroup of GL_n(F3), let N be the vector space of strictly upper triangular matrices, and identify the affine slice I + N with U. For n >= 2,

    A (I + N) B^-1 = I + N

holds if and only if A and B are upper triangular and have the same diagonal entries.

Proof. Taking I gives A B^-1 = u in U, hence B^-1 = A^-1 u. Consequently A U B^-1 = U is equivalent to A U A^-1 = U. The normalizer of U is the invertible upper triangular group: the successive fixed-space filtration of U recovers the coordinate flag, and any normalizer preserves that flag. Conversely upper triangular matrices normalize U. Since A B^-1 lies in U, the diagonals of A and B agree. The converse is immediate. The argument works directly over F3; it does not use an algebraic-closure assumption.

Equivalently, exact preservation of a marked unitriangular affine slice does not merely require the relative matrix A B^-1 to be unitriangular. It also fixes the common flag in which both gauges are triangular. This stronger requirement is the actual mathematical output of the marking operation.

For a four-layer alternating upper/lower chain, write its gauges A0,...,A4. Requiring

    A_i U_i A_(i+1)^-1 = U_i

with U_i alternately upper and lower forces every interior A1,A2,A3 to be diagonal, because each belongs to both opposite Borel groups. Diagonal equality propagates across the chain. Therefore the endpoint relative matrix A0 A4^-1 ranges only over U+ U-, rather than over the advertised four-factor product U+ U- U+ U-. For n = 2, a product in U+ U- has form

    [1 + a b, a; b, 1].

The determinant-one matrix [0,-1;1,0] is not in this set. It does admit longer elementary factorizations, so this counterexample concerns the proposed compiler and not the group-factorization theorem.

This exact calculation prevents substituting a correct bounded elementary-factor theorem for the missing fixed-tensor encoding. Replacing the fixed affine slices by transported, unknown intermediate slices could repair the algebraic relation, but constructing those slices inside one ordinary or one-sign TI instance has not been achieved here.

## Paired block swaps

The previously proved ordinary-controlled helper swap does not test the relative determinant sign of its two blocks. Given a transporter g, one can choose the swap representative using g in one direction and its inverse in the other; for this representative the local determinant contributions cancel, leaving the physical block-permutation sign determined by dimension parity. An arbitrary swap can differ from that representative by block stabilizers, whose determinant contributions must also be included. Cancellation for every swap follows when those stabilizers are sign-neutral, as in the sign-rigid or determinant-neutral helper blocks used here. The same qualification applies to closed matching cycles: relative determinant ratios telescope, but stabilizer contributions need not disappear unless they are neutral. More elaborate use of repeated raw blocks may change which matching permutations are allowed, but this inverse-based swap construction does not read the relative sign of a sign-rigid comparison.

This does not exclude an arbitrary pair-dependent many-one construction. It shows why these particular constructions have not provided one.

## Sources and search scope

The federated DAG front door was queried for determinant conjunction and transporter linearization, covering the registered source catalogs and notes. Relevant prior material includes the conjunction packet Algebra.md and Twists.md, the recorded circuit-to-TI gate work, and the supplied-transporter warning in the route ledger. Source-only search matches were not treated as checked theorems. No Lean formalization or new novelty claim was attempted.

A complete finite control checked all 2,304 ordered pairs from GL_2(F3), finding exactly the 36 pairs predicted by the affine-slice stabilizer theorem. This corroborates the dimension-two calculation only; the proof above establishes the general statement.
