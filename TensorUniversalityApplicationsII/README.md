# Four further applications of tensor isomorphism universality

The [first applications](../TensorUniversalityApplications/README.md) developed low-arity tensor encodings, exact prefix tests, finite-field descent, and stabilized free covers. The four proofs here apply those constructions to group isomorphism, geometric orbit closure, and tensor symmetry.

| Application | Theorem |
| --- | --- |
| [Free tensor encoding of class-two groups](CLASS-TWO-POWER-TENSORS.md) | Finite class-two group isomorphism from succinct central presentations reduces to ordinary free 3-tensor isomorphism over a single congruence ring and over the integers. The encoding covers even order and arbitrary exponents, preserves the central power data, and recovers witnesses. The maximum tensor side on order-$N$ Cayley-table inputs is $O((1+\log N)^3)$. |
| [Witnesses and exact counts for Frattini class two](FRATTINI-SEARCH-COUNT.md) | Deterministic polynomial-time reductions to decision give witnesses, exact counts, and automorphism generators for Cayley-table groups with central elementary abelian Frattini subgroup. For 2-groups this transfers the known $N^{O(\sqrt{\log N})}$ decision bound to these tasks. |
| [Closed orbits from finite-field tensor isomorphism](CLOSED-ORBITS-FINITE-FIELD-TI.md) | At fixed characteristic, finite-field 3-tensor isomorphism reduces to geometric orbit closure intersection for mixed tensor tuples under a product of special linear groups. The tuples use records of order at most three, and every constructed orbit is closed. |
| [Tensor symmetries, restrictions, and spectra](TENSOR-SYMMETRY-TRANSFER.md) | In the stated field regimes, a bounded diagonal resource simulates independent restrictions with tied maps and gives equality of asymptotic ranks. The paper also gives the exact finite-field isomorphism criterion and corrects the characteristic hypothesis of the multilinear congruence theorem over algebraically closed fields. |

The notes give the full written proofs and specify their scopes. Lean receipts cover the named supporting declarations in Lean 4.33.0 with [Mathlib db584cd6](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). The Python scripts replay exact finite controls. Publication priority and external review remain open.
