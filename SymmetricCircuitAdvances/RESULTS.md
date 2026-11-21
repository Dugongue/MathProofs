# Four advances on symmetric permanent and determinant circuits

1. [Exponential permanent lower bound under local alternating symmetries](block-alternating.md). Independent even permutations inside fixed five-label blocks suffice for an exponential orbit lower bound in the number of blocks, in every characteristic other than two, on zero-one inputs.
2. [Exponential monomial-equivariant determinantal complexity](equivariant-determinants.md). The same weak symmetries force exponential order for permutation-equivariant and monomial-equivariant affine determinant representations, including the corresponding Laurent-series border model.
3. [A single reciprocal for symmetric determinant circuits](determinant-reciprocal.md). Polynomial-size rational circuits for the determinant, characteristic coefficients and adjugate preserve simultaneous relabeling and transpose over every field. They use one reciprocal in a nonzero Hankel determinant.
4. [Tight degree-parameter matching bounds](matching-coefficients.md). The optimal orbit size is exponential in \(k\log(1+n/k)\) for principal-permanent coefficients and the weighted \(k\)-matching polynomial, uniformly in \(k\).

The four principal theorems have written proofs. [Lean sources](SymmetricCircuitAdvances.lean) and [verification details](Verification.json) identify the supporting algebra and counting identities that were independently checked. Publication priority is unverified.
