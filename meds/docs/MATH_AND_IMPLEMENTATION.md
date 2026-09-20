# Mathematical scope and implementation bounds

The Lean proof establishes an exact matrix identity over any commutative ring: from A C = P R, R B = I, and P E = I, the matrix C B E is an inverse of A. The second-sided inverse follows from the square-matrix result used by Mathlib. This identity licenses removal of one redundant inverse in the rectangular MEDS construction only when the C data satisfies those hypotheses.

For the row arithmetic candidates, the C code operates on valid reduced representatives of GF(4093). An individual product is at most 4092 squared = 16,744,464. A sum of 256 products is at most 4,286,582,784, below 2^32 = 4,294,967,296. The code narrows intermediates only where the actual accumulated length and reduced-value bounds justify it; inversion power chains retain their wider type. These source-level bounds are not a compiled binary proof, side-channel proof, or proof for arbitrary invalid ABI inputs.

The rectangular and miniMEDS paths also include packed finite-field dot products and tensor contractions. The historical AVX2 path instead keeps its already published broadcast multiplication and applies the narrower row arithmetic. The protocol/build target selects a backend; no secret-dependent runtime selector was added.

The proof is deliberately narrower than the implementation claims. Differential campaigns compare valid key generation, signatures, cross-verification, rejection of mutated signatures, and low-level arithmetic. Their frozen outputs are in evidence. They provide experimental evidence, not universal C verification.

Windows archive repair: five copied MEDS randombytes.c symlink placeholders and one rectangular randombytes.h placeholder were converted to equivalent include directives after the frozen source audit. These files are not compiled by the benchmark harnesses.
