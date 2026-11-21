# Four distant bridges to Grochow's work

These four results use source ideas from the Manin bilinear project, a Heisenberg formalization, tropical assignment algebra, and induced-module coinvariants. The proposed placements are editorial estimates against the existing thirty-result research briefing. They reflect theorem scope, directness of the connection to Grochow, and what the proof adds to the closest work.

| Suggested placement | Result | What the proof establishes |
| --- | --- | --- |
| 6–10 | [Graph isomorphism in one integral tensor genus](ConductorGenus.md) | Three constant primes encode graphs in split integral tensors. Ordinary transporters have exactly four lifts per graph isomorphism, and determinant-one transporters have exactly one lift per even isomorphism. Every tensor of a given size is determinant-one equivalent over the rationals and every finite quotient. |
| 10–15 | [Quantum bases as unmarked class-two groups](TensorBridge.md) | Exact promised Pauli MUBs at any odd prime yield explicit special exponent-$p$ groups. Three auxiliary lines enforce the unitary square class. A normalized ordinary group automorphism count recovers the exact projective unitary symmetry count. |
| 13–19 | [One permanent for hypergraphic matroid intersections](OptimizationBridge.md) | One monotone permanent supplies a sharp $g/(g-1)$ approximation to common independence in two arbitrary hypergraphic matroid unions of incidence girth at least $2g$. A separate optimal-size quadratic max-plus formula gives factor two for maximum spanning tree. |
| 19–24 | [Rotor routing on ribbon covers](TopologyBridge.md) | A unique deck-invariant affine compression of wired rotor dynamics exists exactly when the covering degree is coprime to the base sandpile order. It is natural under changing the base sink, including for covers of arbitrarily high genus with planar base. |

Each main theorem has a written mathematical proof. Lean independently checked the [auxiliary autotopy normalization lemma](AutotopyNormalization.lean) used in the integral construction. The programs and examples in the linked notes are finite controls. Literature comparisons identify the closest sources checked, and publication priority remains open.
