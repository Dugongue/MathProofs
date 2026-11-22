# Four results on determinant-one correction

The determinant ratio $\det X\det Y/\det Z$ of an isotopy between unital associative multiplication tables is the determinant of its normalized algebra isomorphism. This batch uses that ratio to control which ordinary transporters have determinant-one replacements.

| Result | Scope |
|---|---|
| [Supplied correction over finite local rings](D.md) | For every fixed finite commutative local ring with nontrivial unit group, ordinary Tensor Isomorphism over the same ring reduces to correction with a supplied algebra isomorphism. Successful corrections yield original transporters. The determinant obstruction can be a principal unit, including $1+\epsilon$ over the dual numbers over $\mathbb F_2$. |
| [Exact correction for cube-zero radicals](A.md) | For every fixed finite field with more than two elements the supplied problem is TI-hard on centrally indecomposable unital multiplication tensors with radical cube zero. A cyclic action on labelled projective lines makes the determinant image and the number of special-linear orbits exact. |
| [Square-zero radical dichotomy](B.md) | With a supplied ordinary witness, correction is in P in fixed even characteristic and GI-complete under polynomial-time Turing reductions in fixed odd characteristic. The hardness is many-one and the proof computes all three determinant images. |
| [Marked ideals and counting sign edits](C.md) | Over each fixed odd finite field, split étale algebras with overlapping marked ideals realize every binary sign code. The unrestricted orbit count follows from norms and signs. The Hamming-budget repair count is $\#\mathrm P$-complete. |

The ordinary reduction by padding and the earlier supplied-transporter reduction over $\mathbb F_3$ provide the starting point. The new constructions and classifications have written proofs, with separate Lean audits of component statements and finite controls. [Earlier all-field padding proof](https://github.com/Dugongue/MathProofs/blob/main/JouxNarayanan54.lean) · [Earlier $\mathbb F_3$ proof](https://github.com/Dugongue/MathProofs/blob/main/TensorIsomorphismComposition/Results.md) · [Audit](Audit.json)
