# Removing determinant constraints in tensor isomorphism over F3

All results below are informal proofs on explicit input arrays. The unrestricted deterministic polynomial-time many-one chain remains

\[
  \mathrm{TI}\ \le_m^p\ \text{one-sign TI}\ \le_m^p\ \text{two-sign TI}\ \le_m^p\ \mathrm{SL\text{-}TI}.
\]

A reverse reduction here produces one explicit comparison with one fewer required determinant. The covered cases depend on intrinsic data computed from the raw tensors, and the output constraints refer to the same original transporter.

| Reverse step | Sufficient construction |
| --- | --- |
| One sign to ordinary TI | Binary combinations of factor dependencies recover the sign from a split Pfaffian. The right-multiplier extension treats rectangular pencils and an unbounded space of right multipliers. [Factor circuits](OneSignMatroid.md) · [Rectangular version](Multisymmetrizer.md) |
| Two signs to one | The two Koszul defect spaces can be large. Even semisimple multiplicities cancel determinant contributions in the product of the two matrix-mode signs. One of the two signs remains a physical test. [Proof](LargeDefectKoszul.md) · [Multiplicity-only bound](DefectMultiplicity.md) |
| Three signs to two | Intrinsic centroid blocks and a polynomial subset family assemble one mode's determinant, including block permutations. On a local block, even a large mode can be oriented when it has small relative rank over its centroid field. [Centroid blocks](CentroidBuckets.md) · [Local field](CentroidFieldNorm.md) |
| Any adjacent reverse step on the stated domain | An overlapping subspace cover gives two exact sequences on the same carriers. Their determinant factors cancel, leaving small local quotient lines. A raw-slice test recognizes a family with arbitrarily many overlaps and two large tested modes. [Proof](OverlappingCovers.md) |

The determinant polynomial version of the factor-circuit rule also treats the product of the two matrix-mode signs in a square pencil. This gives a second construction for the middle or upper gap on its split-factor domain.

## Combine the centroid constructions

Let the primitive centroid blocks of a concise tensor be indexed by $i$. Let the local centroid field of block $i$ have degree $e_i$ and let its protected mode have rank $d_i$ over that field. Both are intrinsic. Suppose $d_i=O(\log(2+L))$ and each joint bucket, keyed by its three absolute dimensions and $e_i$, has $O(\log(2+L))$ members. The number of buckets and the absolute dimensions of the protected blocks may grow. On this recognizable domain a single two-sign TI instance suffices for SL-TI, or one fewer sign suffices at either other gap when the protected sign is tested.

To see this, use the raw centroid extraction of the centroid-block proof. Categorize blocks by the displayed key and use its subset family on these buckets. For each field degree present, choose one reference field and align every local field of that degree to it by the primitive-component calculation in the local-field proof. These alignments choose coordinate frames only. No isomorphism is required to act trivially on a field. Use the unmarked norm and semilinear-sign lines of that proof as the singleton determinant lines. Their transporter actions, in the chosen field-expanded bases of the blocks, have exactly the individual determinant factors. Attach the local field, exterior and product data over the original block labels so that their maps are induced by the same block permutation and original transporter. Labels, local roles and the norm-ladder levels can be encoded as coordinate algebras and aggregate modules as in the two proofs. Block profile mismatch rejects before encoding.

All other subset lines are computed from concatenations of these block bases. The wedge maps contribute the signs of the block shuffles regardless of field degree. The sole orientation mark is the raw global volume on the full-set line. Hence individual signs may vary. It is their product, with the block shuffle, that is tested. Each local exterior algebra has base-field dimension $e_i2^{d_i}$, the number of product levels is $O(e_i)$ per block, and the subset family is polynomial. The retained-sign compiler converts this system into one explicit comparison. This combination requires no search for compatible block matches.

## Research sources

The pinned [AgentAlphaXiv step-decomposed verification study](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a1b00f-3a81-791c-98fd-c5daefe85ff8.pdf) supplies the methodological emphasis on keeping the same accepted state across all local tests. The pinned [spectrum-preserving control](https://huggingface.co/datasets/alphaXiv/AgentAlphaXiv/resolve/a63f46066ac16fcb470f41933415e175825b6bcc/papers/01a18d98-2e26-7f67-9f50-c6a86e739e72.pdf) motivates holding the ordinary tensor constraints fixed while accounting for determinant changes. The proofs above establish their algebraic identities independently. No code from the archive is included.

[Chen–Grochow–Qiao–Tang–Zhang, Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5) · [Earlier retained-sign results and exact-lifting bound](https://github.com/Dugongue/MathProofs/blob/main/TensorSignChain/Results.md)