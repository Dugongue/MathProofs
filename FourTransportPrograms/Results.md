# Four directions in tensor isomorphism

This packet develops four proposals with informal proofs. Each has a different input contract. The field degree is variable in the first problem, the tensors are raw in the second, the third includes a theorem recovering a hidden decomposition, and the fourth assumes a known coordinate alignment. The last three sections connect respectively to classical-group TI, tensor decomposition, and monomial tensor equivalence. [Grochow–Qiao, TI-completeness](https://arxiv.org/abs/1907.00309) · [Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2)

## 1. Algebraic degree of a transporter

* Testing one specified extension degree for two finite étale multiplication tables over a fixed finite field is polynomial-time, including when the degree is given in binary and all three determinants must equal one.
* Deciding whether any degree up to a binary threshold works is NP-complete. Factors of the degree select vertices in a Vertex Cover instance. The least degree is hard even to approximate within any fixed factor.
* Among dimension-n pairs, the largest finite minimum degree has logarithm asymptotic to the square root of 2n log n. The same asymptotic holds with determinant-one transporters.
* Over arbitrary base fields the minimum degree is the smallest Galois orbit on bijections of primitive geometric idempotents. The general n-factorial upper bound is sharp. Over finite fields we characterize the entire determinant-one spectrum by Frobenius cycle types, orientation, and trace discriminants. [Proofs and complexity model](FieldDegree.md)

**A sharp encoding theorem.** Fix distinct primes p₁ through pₖ, with k positive. Consider pairs of finite étale algebras which first become isomorphic in exactly those extension degrees divisible by at least one of these primes. The smallest possible common dimension is

$$2^{k-1}\prod_i p_i.$$

This bound permits completely unrestricted auxiliary field factors in both tables. To prove it, let x_d be the difference of the counts of degree-d factors. This is a nonzero integer vector of finite support because degree one must fail. For each designated prime p, taking p-th powers of Frobenius makes the profiles equal. It sends a cycle of length d to itself when p does not divide d and to p cycles of length d/p otherwise. Consequently x vanishes at indices divisible by p squared, and x_r = −p x_{pr} for each r coprime to p. Apply this argument to each designated prime. Writing N for their product, each nonzero block indexed by u coprime to N must have, at ud for each divisor d of N, coefficient equal to x_u times the Möbius function of d divided by d. Thus x_u is a nonzero multiple of N. The positive part of this block alone has weighted dimension at least 2 to the power k−1 times uN. This proves the lower bound. Equality is attained with u=1 and x₁=N by taking the positive and negative parts. At Frobenius power t the difference of fixed-point counts in this construction is N times the product over p of the factors (1−1_{p divides t}). A successful degree makes the difference zero at every multiple of that degree, exactly as required. This answers the unbounded-single-hyperedge encoding question raised in the detailed note for explicit tables. It also gives a concrete limitation on compression that preserves the entire degree spectrum.

**Conjecture.** Over each fixed finite field, threshold extension-degree selection stays in NP for multiplication tensors of unital associative algebras whose radical squares to zero. Hardness already holds on the zero-radical subclass. What is needed is a succinct verification of action on both semisimple factors and radical bimodules at a binary-specified degree.

## 2. Character-carrying reductions

* In odd exterior dimension the upper shadow of every nonzero proper subspace in the middle exterior power has strictly larger dimension. A leading-monomial proof works in every characteristic.
* This gives a first-moment nullity tail for a Koszul flattening of a uniform raw tensor in format (2p+1) by n by n. With D the binomial coefficient (2p+1 choose p), the probability of nullity at least r is at most (1+4D times q raised to D squared/4 minus n), divided by q to the r minus one.
* If D squared is at most 2n and the dimension and character exponents meet the stated coprimality conditions, then for any fixed c one ordinary TI query handles a recognized class omitting at most O(L to the power −c) of uniform single tensors, where L is input length. This includes an infinite family over the field of three elements with all dimensions growing. The rank check is exact on each input. The coverage guarantee concerns unbalanced formats. [Precise bounds, reduction, and conjectures](Characters.md)

**Conjectures.** For fixed p the limiting invertibility probability equals that of an unrestricted random square matrix over the same field. On balanced odd cubic tensors over the field of three elements, a family of polynomial-size equivariant maps can recover the sign on a fraction tending to one. The second conjecture requires a new construction.

## 3. Shared-core matching

* Local matches between independent private blocks have additive effects on their common core. For genuine unrestricted block maps fixing the core action, the possible effects in each local orbit class are translates of one subgroup. Matching compatible blocks and prescribing all three determinant values reduces to deterministic subgroup calculations, including the signs of permutations of equal blocks.
* With core subspaces supplied, primitive centroid idempotents recover indecomposable blocks of a concise quotient. The resulting algorithm decides, finds, and counts transporters in polynomial time at fixed field and bounded core and block dimensions.
* There is an infinite weighted three-tensor family on which all three core lines can be recovered in polynomial time from raw coordinates, even though the full tensor has scalar centroid. Low-degree functions generated from slice minors reveal the core. Arbitrarily assigned lists of allowed block effects can instead encode 3-coloring. Retaining the actual local symmetry groups changes the algorithmic conclusion. [Model, recovery, complexity, and counting formula](SharedCore.md)

**Conjecture.** For each fixed field and fixed bounds on core and quotient block dimensions, every tensor admitting the supported decomposition and concise centroid-indecomposable quotient blocks in the marked theorem admits polynomial-time unmarked TI and SL-TI decision on that promise. A sufficient route is to recover a polynomial-sized collection of compatible core candidates. The weighted family only verifies a special case.

## 4. Measurement masks for monomial TI

* With support and permutations supplied, identification of every diagonal gain ratio reduces to spanning one representable matroid per distinct prime divisor of q−1. The correct prime-power construction can retain information lost by reducing the original incidence matrix modulo the prime.
* With at most two such primes, weighted matroid intersection finds a minimum-cost noiseless identifying mask. It also optimizes a sufficient robust design based on disjoint spanning masks. Its decoder uses no discrete logarithms. The optimal general robust design is a separate optimization problem.
* On matrix supports, minimum cuts give the exact unique recovery threshold and edge-disjoint paths give efficient decoding up to it. Even on these supports the minimum-size mask tolerating one erasure is NP-complete to find in its decision formulation. A full Cartesian support admits an explicit optimal-radius majority decoder. [Proofs, examples, and hardness reductions](Masks.md)

**Conjectures.** Minimum-cost noiseless mask selection for three-way supports over the field with 31 elements is NP-hard. This is the first case proposed here with three distinct prime divisors of q−1. A second conjecture is that binary sign observations on arbitrary three-way supports admit a polynomial-time decoder whenever the observed error count lies strictly below half the true minimum distance. The decoder may assume this promise. The supplied alignment is part of each conjecture.

## Status

The field-degree threshold concerns selection of an extension. It does not establish hardness for ordinary TI over one specified field. The character and shared-core theorems provide restricted results towards Grochow and coauthors' classical-group question. The mask results give exact tools for the diagonal stage of monomial TI. All proofs are informal, and publication priority of the specific theorems has not been established.
