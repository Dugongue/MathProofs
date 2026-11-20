# Lean components for ordinary even-order tensor isomorphism

This packet supports the [almost-all ordinary even-order theorem](../OrdinaryFourTIFusions/EvenOrder.md). The theorem concerns dense balanced tensors over a fixed finite field, with variable even order, a random first input, and arbitrary second input.

- [EvenPhysicalAction.lean](EvenPhysicalAction.lean) formalizes the variable-order ordinary tensor action. For a nonzero source whose stabilizers have scalar mode maps, one transporter gives a bijection between all filtered transporters and the product-one scalar tuples that pass the filters. The determinant of a scalar-adjusted mode map is computed explicitly.
- [EvenFlattening.lean](EvenFlattening.lean) checks covariance of the square-cut flattening, its side dimension, and regrouping around any retained physical mode.
- [EvenReciprocalShear.lean](EvenReciprocalShear.lean) proves that the rectangular crossed contraction is affine under the square-zero shear and that the update preserves the inverse-transpose row pairing.
- [EvenReciprocalLaw.lean](EvenReciprocalLaw.lean) turns the exact shear into a bijection of primal and dual pairs and proves the uniform-average and good-baseline transfer identities.
- [EvenReciprocalRank.lean](EvenReciprocalRank.lean) gives exact image dimensions for one-sided matrix multiplication and bounds the rank lost by composing a square linear map with rectangular multiplications.
- [EvenSingularProjection.lean](EvenSingularProjection.lean) proves surjectivity and covariance of the kernel-form projection. The image of any subspace on which the kernel form vanishes is trace zero, with codimension at most that of the source subspace.
- [EvenSingularColumns.lean](EvenSingularColumns.lean) gives the finite-field dependent-column probability bound used for conditioning the singular projection.
- [EvenSingularPrefix.lean](EvenSingularPrefix.lean) gives equal completion counts for every independent list of fixed length and its exact event law inside a uniform ordered basis.
- [EvenSingularConditioning.lean](EvenSingularConditioning.lean) bounds the change in any event probability by the discarded fraction when conditioning a finite uniform law.
- [EvenCells.lean](EvenCells.lean) proves the exact field-cell ratio test and dimension identity for a supplied cell decomposition, and the reduction of witness recovery to a bounded-torsion correction.
- [EvenCellsSplit.lean](EvenCellsSplit.lean) proves that a tensor product of finite-field factors admits a field decomposition and that tensor products of finite products of finite fields are reduced. This is an algebraic existence result.
- [EvenCellsBlocks.lean](EvenCellsBlocks.lean) identifies the unique active primary coordinate for each cell incidence and verifies that variables inherited from the same source block remain shared across cells.
- [EvenCellsPower.lean](EvenCellsPower.lean) proves that a coordinate power factors through the image of the cell map exactly when it vanishes on its kernel.
- [EvenCellsPrefix.lean](EvenCellsPrefix.lean) replaces each arbitrary-length cell equation by a linear-length chain of ternary rows and proves uniqueness of the auxiliary prefix values.
- [EvenProductCount.lean](EvenProductCount.lean) checks the product-state count over a finite abelian group and the size bound on each table entry.
- [EvenScalarCertification.lean](EvenScalarCertification.lean) proves the scalar stabilizer test once the self-comparison branches are known to cover the stabilizer and their homogeneous subgroups are supplied by generators.
- [EvenFilteredTransport.lean](EvenFilteredTransport.lean) combines those checks to give exact counting after a complete transporter search and a scalar stabilizer certificate. On a yes-instance of order d the unrestricted count is (q − 1)^(d − 1).

The sources were checked using Lean 4.33.0 and Mathlib revision db584cd6d46c92f209a44c0f1c829460d327499d. The audited theorem dependencies use only standard Lean axioms. The end-to-end recognition, coverage, and binary runtime theorems remain to be formalized. The scalar transporter equivalence assumes a certified scalar stabilizer and a verified transporter.

The mathematical dependencies are the [four-tensor coverage proof](../FourTIAlmostAll/FullCoverage.md), its [transporter construction](../FourTIAlmostAll/SearchAndLifting.md), and the [even-order extension](../OrdinaryFourTIFusions/EvenOrder.md). The Lean files use the relevant Mathlib finite product, matrix, and tensor-product APIs.
