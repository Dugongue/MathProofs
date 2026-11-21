# Four consequences of the directional sign-gap theorem

Write \(A\) for three-mode special-linear tensor isomorphism over \(\mathbb F_3\), \(B\) for ordinary ternary TI, and \(D_1\) for the directional sign gap on ordinary-positive inputs. The earlier theorem relates a one-query ordinary compiler for \(D_1\) to the Karp degree of signed nonisomorphism. The four theorems below add new encodings and sharp query bounds. The suggested ranks refer to insertion into the previously circulated list. [Earlier directional theorem](https://github.com/Dugongue/MathProofs/blob/002a1088187a6f9e08e08b3c4fe5d20ba53bee15/TISLDirectionalGap/RESULTS.md)

## Suggested rank 2. One directional instance computes an ordinary YES and an ordinary NO

For any independent ordinary TI queries \(x,y\), a single concise pair with a displayed ordinary transporter has directional answer YES if and only if \(x\in B\) and \(y\notin B\). Two scalar-centroid templates read independent switch signs into two distinct directions. A combined construction uses one local centroid. In particular the construction is unconditional, and under the signed collapse the full directional problem has exactly the degree of the Boolean difference of two ordinary TI queries. It also composes with the guarded path-sum compiler. [Proof](difference.md)

## Suggested rank 3. One fixed localization realizes arbitrary finite-field sign gaps

Set \(R=\mathbb Z[t,s,r_1,r_2,r_3]\) and \(R'=R[1/(r_1r_2r_3)]\). For every explicitly presented finite field, every tensor pair \(x\), and every two prescribed determinant tuples \(\alpha,\beta\), the construction gives one ordinary free tensor pair with identical coefficients considered over the two rings. Over \(R\) it is isomorphic exactly when both tuples are feasible in \(x\). Over \(R'\) it is isomorphic exactly when \(\alpha\) is feasible. The resulting localization defect is therefore exactly the requested signed difference. The output pair is ordinarily isomorphic at every prime localization of height at most five. [Proof](transfer.md)

## Suggested rank 4. Affine profile compilers and sharp directional query counts

Every affine map of the three ternary sign bits can be realized exactly on one concise local-centroid tensor pair, and a supplied ordinary witness lifts explicitly. On ordinary-positive inputs either signed answer can be decided by two nonadaptive directional queries with Boolean decoding, or by three with a positive decoder. These minima are exact in the affine-profile oracle model, where probes access the sign profile through affine maps and the decoder sees only the returned bits. A supplied nonzero ordinary witness sign gives the negative signed answer in one directional query. [Proof and lower-bound model](complexity.md)

## Suggested rank 8. Dimension parity exchanges the two local directional answers

Use independently reframed multiplication tensors of a single commutative scalar-residue cube-zero local algebra over \(\mathbb F_3\), with the stated scalar-centroid radical bimap and split slice. On this family a compiler for the positive answer in even dimension, or the negative answer in odd dimension, exists exactly when signed TI reduces to ordinary TI. The other two compilers exist exactly when signed nonisomorphism reduces to ordinary TI. Over any fixed finite local coefficient ring \(R\) with residue \(\mathbb F_3\), a chosen nonzero socle line gives the same table with unrestricted ordinary \(R\)-TI as target. [Proof and exact promise](algebra.md)

## Verification

The four constructions are written proofs. Lean independently verified the two membership identities and their combination for the ordinary difference. Exact finite controls cover all 51 nonempty ternary affine profiles, all 4,096 affine maps, and specific centroid and localization cases. [Lean source](DirectionalDifference.lean) · [Finite controls](fusion_controls.py) · [Verification](Verification.json)
