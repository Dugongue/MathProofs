# Four extensions of fully symmetric final-digit tensor isomorphism

The starting construction puts arbitrary field tensor data in the final ideal of a commutative Frobenius algebra. It uses the same fixed perfect pairing as a slice in all three modes and lifts source maps to determinant-one block maps. [Starting proof](https://github.com/Dugongue/MathProofs/blob/main/FinalDigitFour/Tensor.md)

| Result | Scope |
| --- | --- |
| [Tensor isomorphism in a fixed Hessian fiber](Tensor.md) | One fixed Hessian determinant in characteristic different from two and three, with common determinant-one normal forms for every invertible slice. Over finite local rings the outputs retain a common lower-precision array. In residue characteristic two they also share every one-variable power map. |
| [Four exact degeneration tests](Geometry.md) | On the constructed symmetric endpoints, ordinary source degeneration is equivalent to ambient degeneration under each of independent ordinary, independent special linear, diagonal ordinary and diagonal special linear. The comparison permits support-rank drops and holds in equal-characteristic and unramified Witt coordinates. |
| [Stabilizer schemes and determinant-one lifting](Stabilizers.md) | In equal characteristic the source stabilizer of a concise tensor is a split quotient of the diagonal special-linear stabilizer on all test algebras. Nonsmooth examples occur in every positive characteristic. Witt lift witnesses are obtained after finite faithfully flat root extensions, with an explicit dual-number obstruction over the base itself. |
| [Exact determinant profiles and transporter counts](Algorithms.md) | Closed formulas for the four transporter counts, all attained determinant tuples, and ordinary-to-special-linear orbit splitting. In odd residue characteristic the exact counts reduce in both directions to the source field transporter count by explicit factors. |

The four theorems have written proofs. The accompanying programs check finite instances and supporting identities. [FrobeniusSquareZero.lean](FrobeniusSquareZero.lean) independently checks the Frobenius identity used for the square-zero obstruction. The notes compare the constructions with the closest primary literature. Priority for the exact extensions remains open. Prepared for MathProofs with AI assistance.
