# Tensor universality applications, third round

The [second round](../TensorUniversalityApplicationsII/README.md) developed power records for finite class-two groups, exact search for Frattini-class-two groups, closed finite-field tensor orbits, and a method for transferring symmetry. These four proofs continue the four directions.

| Application | Theorem |
| --- | --- |
| [Witnesses and exact counts for all finite class-two groups](CLASS-TWO-WITNESSES-COUNTS.md) | On order-$N$ Cayley tables, deterministically finds isomorphisms, counts them exactly, and gives automorphism generators in $N^{O((\log N)^{19/20}(1+\log\log N)^{1/10})}$ time. Uses the constructive restriction interfaces of Sun’s algorithm and the earlier tuned decision bound. |
| [Free modular tensor isomorphism reduces to class-two groups](MODULAR-TI-TO-CLASS-TWO.md) | Uniform deterministic reduction modulo any binary $M\ge2$ with a group of order $M^{O(n_1+n_2+n_3)}$ in central-presentation format. It handles even moduli, nonunit coefficients, and arbitrary radicals. Combined with the previous reverse encoding, this gives equivalence of the succinct problems. |
| [Modular tensor spectra](MODULAR-TENSOR-SPECTRA.md) | Characterizes when forgetting block symmetry is surjective on normalized spectra in positive characteristic. It gives the exact prime-order tied asymptotic subrank behavior over every finite field and every algebraically closed field. |
| [Exact separating degree for Frobenius-linked orbits](DICKSON-SEPARATORS.md) | Finds the exact minimum polynomial-invariant degree distinguishing zero and a basis vector with the cyclic Frobenius records fixed. For $q=p^a$ the degree on the specified mixed linear representation is $p(q^n-q^{n-1})/(p-1)$. |

The four notes give the full written proofs. The Lean receipts identify the supporting declarations checked in Lean 4.33.0 with [Mathlib db584cd6](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d). Python scripts replay exact finite controls. External review and priority remain open.
