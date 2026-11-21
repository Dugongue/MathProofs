# Proofs and DAG connections

The audit used [MathProofs main at ef3248c](https://github.com/Dugongue/MathProofs/tree/ef3248c44a28fcc2e97f90392942083b33dce716) and the linked public proofs. [New checked Lean declarations](Verification.json)

- GP-0349, GP-0377, GP-0379, GP-0381, GP-0479 use central commutator coordinates for Boolean rank one and pencil comparisons. [Class-two group–tensor equivalence](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/FourIsomorphismResults/GroupTensorEquivalence.md)
- GP-0091 combines a finite-module version of the historical checked Fitting and cancellation lemmas in Mathproof.Meta.KrullSchmidtCancellation20260902 with modular determinant lifting. [Free cancellation and tensor reductions](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/FunctorialTensorReductions/PROOF.md)
- GP-0277 extends the tagged quiver transporter to all test algebras. GP-0279 combines intrinsic prefix bond spaces with a fixed-signature compiler. [Autotopy normalization](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/GrochowFarDAG/AutotopyNormalization.lean) · [Compiler](https://arxiv.org/abs/1810.09219)
- GP-0605 adds the checked determinant identity to the coefficient-cut technique of Mathproof.LibraryBridges.Claude.CutRankGateGrowth20260907. [Earlier ROABP closure work](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/ROABPHighPowerRoots/PROOF.md)
- GP-0743 uses monic Boolean quotient reduction with a new forget-variable norm. [Earlier modular IPS](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/GrochowProofTransfersIII/MODULAR-SYMMETRIC-IPS.md)
- GP-0950 turns the Heisenberg calculation into an orbit ambiguity for equal-order regular affine actions over finite fields. [Prior real ambiguity](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/GrochowOrbitAndGroupAdvances/ambiguity.md) · [Heisenberg notes](https://github.com/Dugongue/MathProofs/blob/ef3248c44a28fcc2e97f90392942083b33dce716/GenusTwoGroupEpimorphism/HEISENBERG.md)

The use of a prior Lean declaration as an antecedent does not establish kernel verification of the complete written argument.
