# Determinant records for scalar-centroid cube-zero algebras

All comparisons here are over the original ternary field.

- [Dual relation orientation](DualRelationOrientation.md) transfers the combined determinant to the relation bimap's output sign and gives a single ordinary comparison via its local centroid tests. A sign-preserving five-cycle construction reduces the unrestricted problem to inputs whose two centroids are scalar.
- [First syzygy orientation](FirstSyzygyOrientation.md) reads the sign from small degree-three relation spaces and gives infinite scalar-centroid examples with genuine sign constraints.
- [Signed graph determinant lines](SignedGraphDeterminantLines.md) constructs one determinant line on every transporter for a recognizable class with quadratic-size output and relation spaces.
- [Odd-orbit orientation](OddOrbitOrientation.md) compiles sign from short-tuple orbits, with a scalar-centroid example family having exponentially many effective automorphisms.

The main proofs are written. The unrestricted same-field reduction remains open. Three supporting statements about the five-cycle construction passed independent Lean kernel and axiom checks. [Lean source](RelationOrientation.lean) · [Audit](RelationOrientationAudit.json)
