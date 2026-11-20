# Four tensor orbit results using the Alpöge release

## Single third-order orthogonal tensors

An explicit affine-linear construction sends a pair of tensors under the same diagonal orthogonal group to one third-order tensor in dimension $12n+1$. It preserves exact transporters over every commutative rational base algebra and reflects geometric orbit-closure intersection. Invariants of degree $d$ lift with degree at most $243d$. Composing with Lysikov–Walter’s pair completeness theorem gives TOCI-completeness for a single third-order tensor under diagonal complex orthogonal action. The same note proves a CM Hermitian-to-orthogonal reduction with dimension $1+2sum_i n_i$ and an invariant-extension bound of $21d$. Both use the release’s internal trace Gram construction. [Proof](HermitianToOrthogonal.md) · [Lysikov–Walter, Theorems V.18 and V.21](https://arxiv.org/html/2411.04639v2#S5.SS2)

## Cyclic étale multiplication tensors

For rational étale algebras whose field factors split in a common cyclic extension, a single rank per good prime gives a complete test for rational multiplication-tensor equivalence. With combined dimension $n$ and product of input order discriminants $D$, primes up to $O(n^2log^2(2D))$ suffice under Dirichlet GRH. The algorithm works from rational multiplication tables. It computes the small-prime comparison without constructing a splitting field, and the proof gives a finer bound in terms of permutation-character multiplicities. [Proof](CyclicEtale.md)

## Quaternion multiplication tensors under special linear equivalence

For a batch in a common rational general-linear orbit of a product of quaternion multiplication tensors, one panel of at most $max(1,s)$ small primes preserves all pairwise coordinatewise special-linear comparisons. The rank $s$ is the dimension of a computable squareclass span. The labels also retain a rational signed volume, and neither a transporter nor integer factorization is needed. Dirichlet GRH bounds the prime search. A returned panel has an unconditional rank verification under the common-orbit promise. [Proof](SplitMatrixAlgebraSLPrimeCertificates.md)

## Companion pencils and solvable transporters

For squarefree companion pencils with a split source, both rational GL and rational SL equivalence are determined by families of bounded good-prime tests. The GL proof also gives a local-to-global criterion for rational transporter torsors with connected kernel of trivial rational first cohomology and constant solvable component group. The SL proof handles several competing projectivities by choosing a prime that excludes their entire determinant squareclass coset. [Proof](SolvableTransportersAndPencils.md)

## Verification

The four main arguments are mathematical proofs written in prose. The three arithmetic applications are conditional on the Dirichlet endpoint from the source release. The orthogonal construction uses the release’s trace Gram lemma and is independent of GRH. The trace-form source and Dirichlet endpoints were inspected in the release archive with SHA-256 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`. They await a local end-to-end kernel and axiom audit. [Alpöge’s release announcement](https://alpo.ge/remark.pdf)

Lean 4.33.0 checked the [weighted census lemma](UpperCensus.lean) used for cyclic subgroup inversion. Its transitive axioms are `propext`, `Classical.choice` and `Quot.sound`. This formal verification covers the finite inversion step. The individual notes compare the results with nearby literature, with priority undetermined.
