# Four rank-condenser results for sharp matrix substitutions

The starting pencils agree in their rational canonical forms on all marked coefficient substitutions through size $h$. They can first separate at $m=h+1$. [Starting proof](https://github.com/Dugongue/MathProofs/blob/main/SliceSimilarityFour/Tensor.md)

| Proof | Exact result |
| --- | --- |
| [Exact probe complexity](Spread.md) | At size $m$, any one probe using arbitrary coefficients reveals at most one hidden projective line in an explicit family. The bound is sharp for deterministic and randomized adaptive queries. At wider marked pure-row sizes, finite-field covers give the exact deterministic cost. |
| [Lossless compression of all base-defined probes](Compression.md) | One Moore map compresses the product-output block to at most $rD-r(r-1)/2$ over a finite extension. It preserves the base-defined spectral profiles through size $r$ with known scalar padding and preserves chain-ring Smith profiles after unramified extension. The width is sharp at size $m$. |
| [Deterministic rank-layer probes](Deterministic.md) | A finite condenser family generates a list of rank-exactly-$r$ candidates from an explicit source space. The list catches every comparison with a rank-$r$ discrepancy in that source and yields marked substitution tests at size $mr$. |
| [Scheme-preserving geometric compression](Geometry.md) | A simultaneous tangent–secant projection compresses the embedded finite first rank-drop scheme, including nilpotents. The same-field deterministic width is controlled by the largest tangent dimension and the logarithm of the scheme length, when the finite coordinate algebra is supplied. |

The four main proofs are in prose and have exact finite controls. Lean independently verified the adaptive transcript argument in [ProbeTree.lean](ProbeTree.lean). Priority for the exact statements remains unconfirmed. Prepared for MathProofs with AI assistance.
