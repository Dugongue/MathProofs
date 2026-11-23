# Deterministic algorithms for finite-field tensor isomorphism

These results remove internal randomness from several tensor and related isomorphism algorithms. Each stated density refers to uniform sampling of the first input. An accepted first input can be compared to every target.

The factoring premise, where used, is that complete univariate factorization of a degree \(r\) polynomial over every explicitly presented \(\mathbb F_q\) takes deterministic bit time \(r^{O(\log(r+1))}(\log q)^{O(1)}\). [Earlier applications of the same premise](../QuasipolynomialFactoringFallout/README.md).

| Proof | Deterministic result | Scope |
| --- | --- | --- |
| [Ordinary even-order TI](EvenOrder.md) | Polynomial-time decision and explicit witnesses without a factoring premise. Prescribed determinants can be decided and counted in polynomial time. Under the premise, prescribed-determinant witnesses and decision on the full earlier spectral locus take quasipolynomial time. | The unconditional witness result requires connected geometric support graphs. It covers a fraction at least \(1-32d^2 n^{d/2+3}/q\) for \(d=2h\ge4\), \(n\ge37\). |
| [Ordinary bounded-mode TI](BoundedMode.md) | Under the premise, deterministic quasipolynomial decision for fixed \(k\), including the exact set of extension degrees admitting an isomorphism. Also gives deterministic witness recovery on specified stabilizer classes. | All \(a\times b\times k\) pairs for decision, with all basis changes unrestricted. General witness recovery can still use randomized affine slicing. |
| [Orthogonal and special-orthogonal 3TI](Orientation.md) | Lists all transporters unconditionally in polynomial time at fixed odd characteristic. Runs in quasipolynomial time for arbitrary odd fields under the premise. | Recognizable first-input class with failure probability \(O_s(n^{-s})\) for every fixed \(s\) at fixed odd \(q\). Includes the exact orientation profile. |
| [Simultaneous norms and ordinary two-slice TI](Arithmetic.md) | Deterministic polynomial-time witnesses for simultaneous norms and ordinary two-slice TI in the stated class. Prescribing all three determinants in odd residue characteristic adds factoring of degree at most two under the premise. | Irreducible residue pencils over finite fields and explicitly presented unramified finite local rings. |
| [Transfers to earlier average-case proofs](Audit.md) | Unconditional deterministic witnesses for the earlier algebra and matrix-code algorithms, the unitary three-tensor classifier, and the fixed-field corank-three four-tensor branch. | Preserves the stated source populations or density estimates. Extra prescribed-determinant witness results use the premise where specified. |

The algorithmic and density proofs are written mathematical arguments. [Overlap.lean](Overlap.lean) isolates the cross-product cancellation identity from the even-order proof. Its Lean kernel and axiom audit reported only the standard axioms \(\texttt{propext}\), \(\texttt{Classical.choice}\), and \(\texttt{Quot.sound}\). The written algorithmic theorems are outside that Lean audit.

The balanced dense ordinary three-tensor, cubic-form, and alternating-form average-case questions remain open in this analysis. [Li–Li–Qiao–Tao–Wang, v2 §1.5](https://arxiv.org/html/2604.00591v2#S1.SS5).
