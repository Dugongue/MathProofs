# Four principal-unit determinant results

The fixed-ring correction construction ties the determinant of an algebra automorphism to an action on labelled free lines. These results change its dependence on ring size, vary the ring by quotients, and compute exact determinant images in two more classes.

| Result | Main conclusion |
|---|---|
| [Uniform correction over varying rings](D.md) | Replaces width $|R^\times|$ by a small power-subgroup calibration. Supplied-transporter hardness and witness recovery are uniform over characteristic-two local nonfields, unramified rings of characteristic at least four with residue characteristic two, and local rings of any fixed odd residue characteristic. |
| [Prescribed precision profiles](A.md) | Every compatible sequence of determinant subgroups along a strict chain of quotients of a finite commutative local ring is realized by one free multiplication algebra. The proof tracks which tensor types share each exact label after quotienting. |
| [Square-zero extensions](B.md) | Exact determinant-image formulas for square-zero extensions of finite étale matrix algebras. The supplied-transporter problem is in P for fixed characteristic-two rings and GI-complete under polynomial-time Turing reductions for fixed rings of characteristic different from two. |
| [Single-generator probes](C.md) | The automorphism determinant of $R[t]/(t^d)$ has image $(R^\times)^{\binom d2}$ even when substitutions translate $t$ by a nilpotent constant. Exact ordinary-orbit refinements recover the full unit group and isolate principal-unit power subgroups. |

The articles contain the written proofs. Lean checks component identities, and separate finite controls exercise the constructions and exact counts. [Earlier fixed-ring correction proof](https://github.com/Dugongue/MathProofs/blob/main/DeterminantOneCorrection/D.md) · [Audit](Audit.json)
