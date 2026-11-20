# Consequences of mixed tensor degeneration universality

These written proofs build on the [mixed degeneration and smooth comparison theorem](STAR-COMPILER.md). The new statements have independent internal reviews. Human review, Lean verification, and publication priority remain pending.

| Result | Scope |
|---|---|
| [Linear-width degeneration compiler](LINEAR-WIDTH.md) | One ordinary three-tensor of side \(O_\sigma(n^{\lceil d/3\rceil})\) preserves directional degeneration and the smooth type of the reduced closure at encoded points over every algebraically closed field. The output is a split basic multiplication tensor with radical cube zero. |
| [Strict arithmetic degeneration](ARITHMETIC.md) | Finite-field tensor isomorphism at fixed characteristic, and related arithmetic problems, reduce to strict ordinary degeneration. An affirmative endpoint can be given a prescribed determinantal or two-branch germ. Graph and multiplication-table group isomorphism have linear-side reductions over every characteristic. |
| [Exponential branching](SINGULARITIES.md) | Explicit sparse binary tensors of side \(29s\) have a designated orbit-closure point with \(2^s\) branches, multiplicity \(2^s\), and Cohen–Macaulay defect \(s\), over every algebraically closed field. |
| [Near-minimum-rank degeneration universality](RANK.md) | For fixed \(\varepsilon>0\), the reduction retains its smooth comparison with ordinary rank at most \((1+\varepsilon)N\). A connected indecomposable split basic variant has rank at most \((3/2+\varepsilon)N\), matching the best possible leading coefficient in that class. |
| [Combinations](COMBINATIONS.md) | The arithmetic reduction can retain a prescribed singularity in the near-minimum-rank class. The exponential-branch examples can also be made near-minimum-rank, including sparse binary indecomposable tensors with side linear in \(s\). |

The exact finite replays use Python 3. The linear-width replay checks the section on 36 mixed anchor tuples over \(\mathbb F_2,\mathbb F_3,\mathbb F_5\). The singularity replay reconstructs both binary seed tables and checks 24,389 associativity triples per seed. The rank replay checks the path rank certificates, padding, and scalar-idempotent derivatives, including characteristic two. The arithmetic replay checks Frobenius-guard transporters and rank-one endpoints over the fields of order 4 and 9. The finite controls supplement the written geometric proofs.

The linear-width frame proof was independently reviewed for regularity, intrinsic ranks, and balanced product gauges. The rank proof was separately reviewed for the étale scalar cancellation and the Alder–Strassen sharpness argument. The amplified branching proof uses the cited explicit Kronecker seed. Its connected extension was independently checked for unique hub recovery, the independent block readout, and the rank coefficient.
