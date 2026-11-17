# Three reverse reductions for determinant-constrained tensor isomorphism

Over F_3, ordinary TI reduces to one-sign TI, which reduces to two-sign TI, which reduces to SL-TI. The three unrestricted reverse many-one reductions remain unresolved. The new results below are all informal, deterministic and polynomial-time on the stated domains.

| Comparison | Proved in this pass |
| --- | --- |
| One-sign TI to ordinary TI | For square pencils with a logarithmic-dimensional label space, a recoverable short anchor suffices if its centralizer and the full fixed-label centralizer have the same determinant image. This handles all three determinant constraints in one ordinary TI instance. [Proof](GapOne.md) |
| Two-sign TI to one-sign TI | For two equal even tested modes, compute the paired radical flags, pass to a small intrinsic label quotient, and compare the histogram of Koszul determinant signs. An asymmetric histogram fixes the product of the tested signs on every real transporter. [Proof](GapTwo.md) |
| SL-TI to two-sign TI | If descending castling reaches a logarithmic-sized mode, lock that determinant in a local algebra and read the two remaining signs on the same transporter in one pencil. All three original dimensions may be large. [Proof](GapThree.md) |

For unrestricted inputs, we also realized every linear map on the three determinant bits by an explicit polynomial-size tensor pair. This includes erasing the third bit while preserving the exact set of the first two. Coupled with the prior one-axis construction, it packs an independent two-sign test and a one-sign test into a single SL-TI instance. Thus SL-TI reduces to two-sign TI exactly when two-sign TI is closed under binary conjunction. A polynomial objectwise SL-TI-to-two-sign compiler would give the stronger ordinary TI collapse, via a five-object argument. [Sign projections and conjunction](SignProjections.md)

The signs are always required on a single shared transporter within each original comparison. The verified special cases and composition theorem do not settle [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5). Publication priority has not been established.

The accompanying structural, castling, and neutral-conjunction notes supply previously obtained MathProofs dependencies. Their inclusion is for mathematical context.
