# Research campaign results

All proofs in this packet are informal. The campaign used four workers, compared concrete routes, and subjected the principal arguments to a second mathematical reading. Computational checks test specific finite instances. No Lean kernel verification or publication-priority claim is made.

## 1. Arrow orientation changes constrained epimorphism complexity

Given raw finite-field diagrams A,B,C and prescribed natural maps rho from A to C and psi from B to C, seek a natural map f from A onto B satisfying psi f = rho at every vertex.

For ordinary persistence chains whose arrows all point forward, there is a deterministic polynomial-bit-time algorithm to count these maps exactly and construct one. It also supports exact uniform sampling in expected polynomial time and enumeration with polynomial delay. Raw interval decomposition is included in the proof. Arbitrary simultaneous prescribed maps are permitted by taking their common image. [Ordinary persistence proof](Persistence.md)

For strictly alternating zigzag paths, existence is NP-complete and exact counting is #P-complete under polynomial-time metric reductions over every fixed finite field, including the binary field. Both prescribed maps onto C are surjective. The target's transitions are all surjective, and the source is supplied as explicit intervals. The reduction is from SAT and retains every commuting-arrow equation. [Zigzag hardness proof](Zigzag.md)

This comparison concerns constrained epimorphisms through a prescribed common quotient. Standard barcode and zigzag decomposition remain existing polynomial-time tools. A targeted literature search did not identify this exact comparison, and priority remains unverified.

## 2. Count constrained module surjections without listing the field elements

The underlying algebraic result counts surjective maps from specified truncated-projective source modules over finite rings, subject to prescribed compositions. The count and one witness are computed in polynomial time in compact binary additive coordinates. The proof uses exact affine fibers, projectivity over quotient rings, and a rank dynamic program for nested head spaces. It allows modular group algebras. The required source decomposition and head data are part of this general ring theorem's input. The ordinary-persistence theorem above extracts its own decomposition. [Finite-ring and group proofs](Groups.md)

For Abelian Sylow towers on Cayley tables, this also gives source-or-target exponent conditions for polynomial epimorphism counting. Every two-prime tower instance has an explicit deterministic N to the power O(log log N) algorithm. When the target complement's action kernel splits off, the algorithm is polynomial with arbitrary mixed exponents. The unrestricted published Sylow-tower polynomial-time question remains open. [Question 3(4)](https://arxiv.org/html/2609.07429v1#S7)

## 3. Repeated characteristic-two norm lifting through actual isometry groups

The first matrix theorem solves affine transport on full symplectic natural-module copies and assembles lifting when each factor contributes at only one grade. [Initial theorem](Matrix.md)

The second permits arbitrarily many revisits to one symplectic factor. It maintains exact symplectic, orthogonal or Omega stabilizers, with nondegenerate extracted marking spans and an explicit guard on residual dimension. It uses classical first-cohomology calculations and a constructive quadratic-form extension argument. [Repeated-grade theorem](Round2Matrix.md)

The third handles a degenerate intermediate marking consisting of one fixed symplectic vector, through an explicit cocycle calculation for its actual stabilizer. Its two-grade norm corollaries cover checked split quotients and direct sums of the genuinely nonsplit quotient V/Ev, with optional trivial summands. [Point-stabilizer theorem](Round3Matrix.md)

The unrestricted characteristic-two tuple-isometry question remains open, in particular for general nonsplit marked quotients and repeated arbitrary degenerate markings. [Published question](https://arxiv.org/html/2611.00735v1#S1.SS4)

## 4. Integer homology has hard counting with efficient enumeration

On unweighted orientable surfaces with unary integral input coefficients, counting minimum integer absolute-value representatives of a prescribed homology class is #P-complete and approximation-equivalent to counting bipartite independent sets. The proof represents every optimal face labeling by an ideal of a residual cut poset and supplies a count-preserving converse surface construction.

With binary coefficients, uniqueness, finding a second optimum, and polynomial-delay enumeration remain polynomial. That enumeration statement extends to every explicitly given totally unimodular boundary matrix with positive rational weights. Exact counting is already hard on the surface subclass. [Proof](IntegerCycles.md)

These are statements about integer absolute-value optimization. The earlier binary-field support problem has a different complexity. Integer optimization itself was already established by Dey, Hirani and Krishnamoorthy. [Classical optimization theorem](https://arxiv.org/abs/1001.0338)

## 5. Counting antichains of small-rank geometric lattices

Counting antichains of explicit geometric lattices of rank three is #P-complete under metric reductions. Testing oddness is parity-P-complete, even when each line has at most three points. The constructions supply rational projective representations, or representations over a prime field whose prime varies with the input. These are counts of antichains in the lattice of flats. [Geometric-lattice proof](GeometricLattices.md)

The companion note proves sharp height-four and dimension-three thresholds for arbitrary finite lattices and credits the existing deterministic approximation algorithm on incidence lattices. [Threshold proof](Posets.md)

The separate explicit-distributive-lattice question remains open. The campaign rejected exponential ideal-completion and information-losing coordinate-closure routes. A positive subexponential enumeration bound from the existing width theorem is recorded with attribution. [Distributive-lattice checkpoint](DistributiveLattices.md)

## Evidence and scope

The integer proof passed 91,815 threshold identities, 1,728 ideal-penalty cases and 3,279 median-pairing checks. The nested affine-column rank distribution passed 750 comparisons with exhaustive matrix enumeration. The lattice and zigzag notes record their own independent finite checks. The group and matrix notes retain exact hypotheses and sources for every inherited theorem.

The principal developments are broader algorithms and explicit complexity classifications. No newly identified published open question is asserted fully closed in this packet. The proofs, partial scopes and credited older results are provided together so the mathematical conclusions can be assessed directly.

The earlier [chamber construction](Chambers.md) and [projective-layer recursion](ProjectiveLayers.md) are included as dependencies. They retain their citations.
