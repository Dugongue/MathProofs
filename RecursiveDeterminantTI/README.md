# Recursive reductions from determinant-constrained TI to ordinary TI

These written proofs give polynomial-size reductions to one ordinary three-tensor isomorphism instance over the original field \(\mathbb F_3\) on their stated domains.

- [Cube-kernel splits](RecursionSyzygy.md) use exact sequences for an intrinsic subspace, its quotient and the mixed relations. There are both-scalar-centroid examples of unbounded depth.
- [Symplectic factorization and cropped duality](RecursionMorita.md) alternate between symmetric and alternating products. The relation spaces can be large at every step, and the determinant constraint can change the answer.
- [Principal adjoint filtrations](RecursionAdjoint.md) handle mixed module lengths and unbounded radical length over a truncated polynomial adjoint algebra. The parity test chooses which small side of each exact sequence to read.
- [Unordered graph modules](RecursionGraph.md) allow repeated isomorphism types. The [independent hierarchy theorem](RecursionTree.md) handles arbitrary depth and branching by one global signed switch system.
- [Combined recursion](CombiningRecursions.md) links the determinant of the same transporter across cube splits and symplectic steps. It gives both-scalar-centroid examples using both kinds of step at unbounded depth.

The main reductions are informal. Three supporting parity and calibration identities passed an independent Lean kernel and transitive-axiom audit. [Lean source](RecursiveDeterminants.lean) · [Audit](RecursiveDeterminantsAudit.json)

The unrestricted ternary case remains open. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)
