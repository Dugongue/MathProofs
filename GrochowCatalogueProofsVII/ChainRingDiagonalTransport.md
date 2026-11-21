# Exact diagonal transport for chain-ring codes of arbitrary Smith type

## GP-0339

For linear codes over $R=\mathbb Z/p^e\mathbb Z$ with arbitrary Smith types, a prescribed permutation can be tested for a lift to a monomial transporter in deterministic polynomial bit time. If a lift exists, the algorithm returns it and describes all possible diagonal lifts by a linear submodule and a disjoint coordinate partition of its residues. The running time is polynomial in the presentation sizes and $\log(p^e)$. In particular, a matching procedure for the residue and socle layers can be followed by an exact lift test on each candidate permutation using the given code generators.

First apply the chosen permutation to the source code. Determine the sizes of $C,D$ by Smith reduction and reject unequal sizes. Form the linear submodule
$$
S=\{x\in R^n\mid \operatorname{diag}(x)C\subseteq D\}.
$$
This is a system of linear congruences in $x$: apply the quotient map $R^n\to R^n/D$ to the coordinatewise product of each source generator with $x$. Smith reduction with valuation-minimal pivots gives generators of $S$ and their lifts. A vector $x\in S$ gives an isomorphism precisely when all coordinates are units. Sufficiency follows from invertibility of $\operatorname{diag}(x)$ and the equality of code sizes. Thus we need one nowhere-zero vector in the image $U$ of $S$ under entrywise reduction to $k=\mathbb F_p$.

This full-support test admits a deterministic solution because of the structure present whenever an invertible lift exists. If $x_0$ is such a lift, then
$$
S=x_0A,\qquad A=\{a\in R^n\mid \operatorname{diag}(a)C\subseteq C\},
$$
where multiplication is coordinatewise. The set $A$ is a unital $R$-subalgebra of $R^n$. Its residue image is a unital $k$-subalgebra of $k^n$, and any such algebra consists exactly of the vectors constant on a partition of the coordinates. To prove this, identify coordinates whose evaluations agree on the whole algebra. For one block and each different block choose an algebra element separating them. Subtract its value on the other block and divide by the difference of its two values. Multiplying these elements gives the indicator of the first block. This produces every block indicator using only algebra operations.

It follows that if an invertible lift exists, $U$ is spanned by vectors supported on disjoint blocks, one nonzero line per block, with nonzero value at each coordinate in its block. Conversely that structure guarantees a nowhere-zero vector in $U$. Recognize it as follows. For a basis of $U$, view each coordinate evaluation as a row functional on its coefficient space. Reject any zero row. Group proportional rows and choose one representative of each class. If the representatives are dependent, the required structure is absent and there can be no invertible lift, by the preceding argument. If independent, solve the linear system making every representative evaluate to one. All coordinates of the resulting vector are nonzero. Lift its coefficients using the generators of $S$ used to construct the residue basis. This yields a unit vector in $S$ and hence an exact transporter. Multiplication by the returned transporter identifies all lifts with the unit vectors in $A$, whose residue coordinates are constant and nonzero on its blocks. The residue and congruence computations do not require an expanded ring or codeword list. [Related witness-preserving code comparisons](https://github.com/Dugongue/MathProofs/blob/53ffa5dcacaca5757e11adca8df99ba0d38f8bc5/GrochowCatalogueProofsII/CodeEquivalenceAndOracle.md)
