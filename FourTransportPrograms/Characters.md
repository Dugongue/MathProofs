# Determinant characters of random Koszul flattenings

For an explicit family of tensor formats we prove a finite-field coverage estimate for a one-query reduction from special-linear to ordinary tensor isomorphism. It applies when all three dimensions grow. The existing determinant-line method handles an input with small corank. The new step is to bound that corank's tail from the raw uniform distribution. The operations and probability estimates below are informal mathematics. [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2) · [Koszul and Kronecker–Koszul flattenings](https://arxiv.org/abs/2602.12762)

## Theorem 1. Strict expansion in the two middle exterior powers

Over any field let A have dimension a = 2p+1, with p at least one, and let D be the common dimension of its p-th and (p+1)-st exterior powers. For a nonzero proper subspace H of the p-th exterior power, let A ∧ H denote the span of all elementary wedges with a vector in A. Then

$$\dim(A\wedge H)\geq \dim H+1.$$

Choose a basis of A. Row-reduce a basis of H on the ordered squarefree monomials of degree p. Use lexicographic order, which preserves comparisons when the same unused index is inserted. The leading monomials form a family of size dim H. Every (p+1)-subset extending a leading monomial occurs as a leading monomial in A ∧ H, by wedging the corresponding basis vector of H with the missing index. Distinct leading terms give independent vectors. This remains valid in characteristic two.

The bipartite containment graph between the two middle levels of the Boolean lattice is connected and regular of degree p+1 on both sides. A subset of the left side has at least as many neighbors as vertices by counting edges. Equality for a nonempty proper subset would disconnect its vertices and neighbors from the complement. The strict inequality proves the claim.

## Theorem 2. A kernel tail for random raw tensors

Put T in A ⊗ B ⊗ C with dim B = dim C = n over the field with q elements. Define a square map of size nD,

$$K_T:B^*\otimes\Lambda^p A\longrightarrow C\otimes\Lambda^{p+1}A,$$

by contracting its first argument with the B component and wedging the result's A component with the exterior argument. Draw all entries of T independently and uniformly. Write h for the nullity. For every integer r at least one,

$$\Pr[h\ge r]\leq\frac{1+4Dq^{D^2/4-n}}{q^r-1}.$$

Indeed a kernel candidate is an n-tuple of vectors in the p-th exterior power. Let H be their span, of dimension s. For one coordinate of the C mode its image is uniform on A ∧ H, by surjectivity of the map sending n independent A-vectors to the sum of their wedges with the prescribed tuple. The n coordinates are independent. The probability of getting zero is therefore q to the power minus n times dim(A ∧ H). For a fixed H at most q to the power ns tuples span it. The full-space contribution to the expected number of nonzero kernel vectors is at most one. Every nonzero proper H contributes at most q to the power minus n by Theorem 1. The number of s-dimensional subspaces is at most four times q to the power s(D−s), by the Gaussian binomial formula and the product bound for q at least two. Summing gives the displayed numerator. A kernel of dimension r contains at least q to the r minus one nonzero vectors. Markov's inequality finishes the proof.

## Theorem 3. An ordinary TI query on the small-corank locus

Assume that a, n, and D are units modulo q−1. Use the ordinary covariant tensor action on all three modes. For an original transporter g let its mode determinants be x, y, z. They can all be corrected to one by scalars preserving the tensor whenever

$$\chi(g)=x^{a^{-1}} y^{n^{-1}} z^{n^{-1}}=1,$$

with exponents modulo q−1. Conversely an SL transporter itself satisfies this constraint. The determinant ratio of the induced maps on the target and source of the square flattening is the character to the power nD. To verify this, the determinant exponents on the three modes are nD/a, D, D. The first follows by subtracting the two exterior-power determinant exponents, or by the binomial identity D/a = (2p)!/(p!(p+1)!). The dual action on B gives a positive exponent D in the ratio. Since nD is a unit, requiring ratio one suffices.

When both flattenings are invertible, one compares their determinants and, if equal, asks ordinary TI on the original tensors. For equal positive corank h choose source ambient bases (kernel, complement), and target ambient bases (image of complement, cokernel lifts). Write t_T for the ratio of the determinants of these target and source bases in the original ambient frames. Do the same for S. The desired ratio on any intertwiner is

$$ (t_S/t_T)\,\det(g_{\rm coker})/\det(g_{\rm ker}). $$

The complement-to-image determinants cancel. Attach the actual kernel inclusion and cokernel projection, their exterior powers, and a linear map from the top kernel line to the top cokernel line with scalar 1/t_T on input T. The same construction on S enforces ratio one. The original transporter lifts whenever its ratio is one, since its action induces the maps on all exterior spaces. Exterior multiplication by vectors forces these actions inductively. A rank mismatch is an immediate rejection.

All the data are linear and bilinear maps on named spaces. The exterior powers of A up to degree p+1, the tensor products, dual pairings, and kernel/cokernel constructions can be written with size polynomial in the input length L, D, and 2^h, since a=2p+1 and the largest exterior dimension is D. For a fixed-signature encoding, combine the named spaces in a direct sum, with a coordinate algebra of mutually orthogonal idempotents acting by the summand projections. Mark its first basis element and the shift to force all idempotents individually. Named input and output copies keep distinct maps in disjoint blocks of a joint bilinear map, with identities tying copies. This yields a fixed-signature tensor system with polynomial encoding size, to which the trivalent tensor-system reduction applies. The algorithm therefore constructs one ordinary TI instance on the promised small-corank locus. This argument extends the project's earlier first-Koszul determinant-line construction to the middle exterior powers. [Tensor-system reductions](https://arxiv.org/html/2306.03135v2#S4)

## Corollaries and scope

* If D squared is at most 2n, the numerator in Theorem 2 is at most 1 + 4D q to the power −n/2. Accept all coranks less than the ceiling of c log base q of L, for any fixed positive c and L sufficiently large. Then the exceptional fraction is O(L to the power −c). The detector reads the raw tensor, and all recognized pairs have a deterministic polynomial-size reduction under the unit hypotheses. The random statement concerns coverage, while the reduction on its recognized domain is exact. For random pairs, use the union bound, or just one tensor if the second is an isomorphic copy.
* The determinant comparison alone covers at least 1 − (1+o(1))/(q−1) of single tensors under this growth bound. It can be uninformative at q=2, where the ordinary and special-linear groups already coincide.
* An infinite example has q=3, p=2^j−1, and n any odd integer at least D squared. Then a and n are odd and D is odd by the binary binomial parity criterion. All three dimensions can tend to infinity. These are unbalanced formats. The bound supplies no coverage estimate for n by n by n tensors.

## Conjectures

1. For each fixed p and finite field, as n tends to infinity the probability that the middle Koszul map is invertible tends to the nonsingularity constant for unrestricted uniform square matrices over that field. The first moment above is compatible with this prediction. A second test would compare the contribution of independent pairs of kernel vectors.
2. For odd cubic format over the field with three elements, there is a uniformly polynomial-size construction of equivariant linear maps for which the small kernel and cokernel determinant lines jointly recover the product sign on a fraction tending to one. A construction must compute the maps from the raw input, specify the transformation characters, and give quantitative coverage. Even success in distribution would leave the worst-case question open.
