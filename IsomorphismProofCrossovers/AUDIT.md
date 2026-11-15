# Four crossovers for isomorphism and proof complexity

The four documents give AI-assisted informal mathematics. The proofs state their source models and algorithmic bounds explicitly. Publication priority remains unestablished.

| Proof | Exact finding | Main audit point |
|---|---|---|
| [Polynomial Calculus with inversion](circuits.md) | Every inconsistent polynomial system refutes at its maximum axiom degree with one inversion inference. Geometric 3-tensor nonisomorphism has degree at most three, contradicting Galesi–Grochow–Pitassi–She's Conjecture 1.7. | Section 2.3 allows one reversed-product entry and arbitrary polynomial substitutions. All antecedents are original axioms or zero. The matrix side is one plus the number of axioms. The Nullstellensatz multipliers in the substitution can have high degree and size. |
| [Central radicals and perfect products](groups.md) | Deterministic polynomial Cayley-table isomorphism with witness, coset and count for both product-quotient branches of Grochow–Qiao Theorem 7.1 with arbitrary abelian centers. | One cohomology alphabet at each factor has polynomial size in that factor alone. The bit-vertex budget is the sum of logarithms. A common permutation must pass all scalar codes. The permutation-kernel case in Open Problem 8.3 is broader. |
| [Balanced orthogonal and unitary reduction](tensor.md) | A constant-free ordered $d$-to-$3$ reduction over involutive fields, with total side dimension $O(n^{\lceil d/3\rceil})$. | The twelve named blocks have distinct wiring and preserve exact independent leaf actions after dividing out the three norm-one pin factors. Rank and orthogonal complements recover all blocks without any anisotropy assumption. |
| [Sharp quartic invariant degrees](closures.md) | Explicit closed orbits in one symmetric balanced quartic representation first separate in exact degree $((3n+1)2^n-(-1)^n)/9$. The maximum nonnegative null-cone detection degree has order $n2^n$. | Root-free weight support establishes moment-map vanishing after rescaling. Total unimodularity gives the upper bound only for nonnegative support. Circuit size and general orbit-closure running time are distinct measures. |

The [inversion companion](circuit-ips.md) charges arithmetic circuits for the substitutions. It gives polynomial-size translations to and from the Ideal Proof System. The forward translation follows from an adjugate identity valid even for singular matrices. It preserves earlier certificates through circuit sharing. The reverse translation uses a division-free gatewise difference quotient followed by the same single inversion. Formal identity checking remains part of the circuit-annotation model.

The finite checks in `check_controls.py` replay 87 inversion block fixtures, 98,304 mixed-exponent coefficient and bit-edge comparisons, and 78 quartic weight recurrences. The tensor proof records its separate exact finite-field fixture. The general results rest on the written proofs. These controls do not implement the algorithms or give Lean certificates.

## What the DAG contributed

- Orbit-closure invariance and the Schur-block identities suggested the first inversion construction. The stronger final proof needs only the Nullstellensatz and a block shear. Prior tensor trace certificates use the same discipline of charging only actual derived polynomial lines.
- The prior abelian extension and finite-ring work gives the fixed-map decoder and coefficient orbit compression. Schur-multiplier and cohomology lookup motivated bounding the scalar cohomology alphabet by the quotient factors. The numerical generator bound comes from Grochow–Qiao Lemma 7.9, not from a formal import.
- The balanced ordinary tensor reduction supplies named prefix products and cyclic labels. Classical-group rank markers and conjugate identity wires transfer that compiler to standard forms.
- The all-minors determinant property of totally unimodular matrices was found in a project branch on permanent and determinant bounds. A quartic weight is a sum of two incidence columns, turning that property into a bound on the primitive balancing relation. Contraction and moment-map results supply the other half of the argument.

The federated lookup was used for discovery across registered source catalogs, the typed DAG and notes. Source-only hits and written controls are separate from checked theorem evidence. The proofs reproduce their elementary constructions and cite the published results they invoke. The payload includes the project-authored fixed-quotient companion manuscript and no third-party code.
