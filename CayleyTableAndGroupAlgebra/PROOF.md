# Cayley-table algorithms and modular group algebra factors

The earlier Cayley-table lower bound used explicit affine coordinates to count valid tables within isomorphism classes. These follow-ups take the same approach to different information problems. An explicit basis makes it possible to process Cayley-table data without retaining all its coordinates. A power filtration isolates central factors. Small-support relabellings give many tables that agree on sampled positions.

| Informal proof | Exact result |
| --- | --- |
| [Count-free Weisfeiler–Leman for unique decompositions](UniqueDecompositionCountFreeWL.md) | Johnson, Levet, Vojtěchovský and Widholm, Question 7.1. Groups with a unique fully refined decomposition and boundedly generated indecomposable factors have bounded count-free dimension and $O(\log\log n)$ Version II round complexity. |
| [Constant-round counting Weisfeiler–Leman](ConstantRoundCountingWL.md) | Johnson, Levet, Vojtěchovský and Widholm, Question 7.2. Bounded-dimensional, constant-round counting Version II identifies groups with boundedly generated indecomposable factors, without a uniqueness assumption. |
| [Fully refined group decomposition](DirectProductDecomposition.md) | Johnson, Levet, Vojtěchovský and Widholm, Question 7.3. Every finite Cayley-table group admits a deterministic FL algorithm for a fully refined internal direct product decomposition. Canonization for groups with boundedly generated indecomposable factors also lies in FL. |
| [Central quasigroup isomorphism](CentralQuasigroupIsomorphism.md) | Johnson, Levet, Vojtěchovský and Widholm, Question 7.5. A deterministic L algorithm recognizes central quasigroups and tests their isomorphism from the multiplication tables. |
| [Commutative factors of modular group algebras](CommutativeGroupAlgebraFactors.md) | García-Lucas, del Río and Sakurai, Remark 7. Over any characteristic-p field, every commutative tensor factor of a finite p-group algebra comes from an abelian direct factor. An additional argument reproves Sakurai’s existing answer to Question D. |
| [Sharp Cayley-table completion bounds](CayleyTableCompletion.md) | Huh, Open Problem 2. Under the displayed scalar-coordinate observation model, the proposed sample rate is impossible even if the group type is known. The sharp worst-case rates are $\Theta(n^2\log n)$ scalar observations and $\Theta(n\log n)$ whole cells. The whole-cell guarantee for the specific flatness optimizer remains open. |

These proofs are informal. Their source problems and prior results are attributed in the individual files.
