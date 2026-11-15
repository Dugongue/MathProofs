# Group, graph, and tensor isomorphism crossovers

These are AI-assisted informal proofs. The articles give complete statements and distinguish known ingredients from the new constructions.

| Theorem | Scope |
| --- | --- |
| 1. [Arbitrary abelian-kernel lifting](AbelianKernelLifting.md) | A supplied quotient isomorphism can be lifted, counted, and represented by a coset in deterministic polynomial Cayley-table time. Resolves Skresanov's generator-bound question and the requested extension of Theorem 6.11 in Grochow–Qiao Open Problem 8.1. |
| 2. [Succinct Fitting-free epimorphism hardness](FittingFreeQuotientCrossovers.md) | NP-completeness and metric #P-completeness from permutation generators. Decision remains hard on a family with polynomial-time group isomorphism. |
| 3. [Graph parity in a square tensor](SparseGraphTensorTransporters.md) | An $(n+15)^3$ tensor construction makes the product of the three transporter determinants equal the sign of the graph isomorphism. Its odd-characteristic special-linear problem tests even graph isomorphism. |
| 4. [Decoding from raw tensors](RecoveringGraphTensors.md) | Recognizes the two encoded tensor families and recovers the underlying graph and an explicit change of basis. Deterministic over $\mathbb Q$ and fixed finite fields. |
| 5. [Linear proof degree for sparse cubic forms](SparseCubicProofComplexity.md) | Linear PC degree for equivalence of $O(n)$-monomial cubics in $n$ variables in characteristic different from $2,3$, and linear SoS degree over the reals. |
| 6. [Entire Frattini quotient cosets](FrattiniCosetLiftingAndApplications.md) | Polynomial constructive lifting and counting when the permitted quotient automorphisms have bounded nonabelian composition-factor orders. |
| 7. [Group isomorphism above a Fitting-free quotient](FrattiniCosetLiftingAndApplications.md) | Polynomial decision, search, and counting when the Frattini quotient is Fitting-free and its socle has bounded multiplicity of each simple type. The Frattini kernel is arbitrary. |
| 8. [Coprime epimorphism counts](CoprimeEpimorphismCounts.md) | Colored code transport gives exact counts and witnesses with elementary abelian Hall Sylows and elementary abelian complement. The target is arbitrary. |
| 9. [Full stabilizers of symmetric trilinear forms](SparseGraphTensorTransporters.md) | A single linear action realizes the graph automorphism group times $F^\times$ in characteristic different from $3$. The characteristic-$3$ kernel is explicitly determined. |
| 10. [Fitting-free quotient lattice](FittingFreeQuotientCrossovers.md) | The full lattice of Fitting-free quotient kernels is distributive and is determined by the poset of monolithic Fitting-free quotient kernels. |

[Computing and lifting through the Frattini subgroup](GeneralFrattiniComputationAndLifting.md) supplies the deterministic Cayley-table algorithm used in the Frattini results. The articles also include the rectangular tensor transporter, a bounded-target-rank epimorphism algorithm, and a second Frattini-quotient isomorphism algorithm.
