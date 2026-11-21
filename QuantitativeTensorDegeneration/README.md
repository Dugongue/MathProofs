# Quantitative tensor degeneration

Four written proofs quantify the cost and geometry of a single degeneration of a specified pair of tensors. Unless otherwise indicated, \(t\) is the formal Laurent parameter over the original field.

| Result | Main conclusion |
| --- | --- |
| [Sparse exponential poles](SparseExponentialPoles.md) | Concise binary tensors of side \(N\) with \(O(N)\) nonzero entries admit an orbit arc linear in \(t\), while every Laurent three-mode presentation needs a forward entry pole of size \(2^{\Omega(N)}\). The minimum polynomial approximation order is exponential as well. |
| [Laurent recovery](LaurentRecovery.md) | The fixed-signature mixed-to-ordinary compiler preserves and reflects the least symmetric pole depth up to dimension-independent factors. Recovery costs at most six times the ordinary witness depth and uses linearly many input coefficients per entry at fixed signature. A quantitative symplectic retraction transfers the sparse lower bound. |
| [Exact pencil profiles](ExactPencilProfiles.md) | Exact optimal Smith profiles, determinant excess, pole depths, and polynomial approximation orders for ordered cyclic-source pencils and split semisimple-to-nilpotent pencils with moving labels. Each strict comparison admits error degree one. |
| [Determinant-resolved transporter fibers](TransporterFibers.md) | The linear-width Peirce compiler and the 29-dimensional pencil construction admit explicit transporter scheme products over arbitrary commutative rings, also with prescribed tensor-mode determinants. This gives determinant-one degeneration and exact finite-ring stabilizer counts in the stated cases. |

The first result separates the degree of the tensor-valued arc from the order needed to present it using polynomial mode maps from the given source. The source is a specified unital multiplication tensor. The border-rank question studied by Ganesh, Koiran, and Oliveira uses the diagonal rank tensor as the source. [Polynomial Bounds on Degeneration Order from Commutativity Properties of Tensor Slices](https://arxiv.org/abs/2608.10179)

The previous projects supply the mixed top-relation compiler, the linear-width Peirce compiler, and hyperbolic padding. The exact pencil formulas address witness costs, whereas the earlier pencil depth result counts strict steps along a chain. [Mixed tensor degeneration](https://github.com/Dugongue/MathProofs/blob/main/MixedTensorDegenerations/DEGENERATION.md) · [Linear-width compiler](https://github.com/Dugongue/MathProofs/blob/main/TensorDegenerationFallout/LINEAR-WIDTH.md) · [Symplectic orbit closures](https://github.com/Dugongue/MathProofs/blob/main/SymplecticTensorFusions/OrbitClosures.md) · [Pencil degeneration chains](https://github.com/Dugongue/MathProofs/blob/main/KroneckerDegenerationDepth/Proof.md)

The [Lean companion](QuantitativeIdentities.lean) checks five supporting identities. Its [audit receipt](QuantitativeIdentitiesAudit.json) gives the source hash, toolchain and transitive axioms. The four main proofs are written, with scoped arithmetic checks recorded in their respective files. Publication priority remains open.
