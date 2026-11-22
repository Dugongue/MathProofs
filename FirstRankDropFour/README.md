# Four extensions of projective schemes at the first rank drop

The starting construction realizes an arbitrary projective scheme at the first extra-relation size $m=h+1$ of a marked first-row substitution. The full locus is its product with the split maximal orthogonal Grassmannian. [Starting proof](https://github.com/Dugongue/MathProofs/blob/main/SharpSubstitutionFour/Geometry.md)

| Proof | Result |
| --- | --- |
| [Several schemes in one pencil](Windows.md) | Independently chosen projective schemes occur at separated sizes in the same pencil. The schemes occur on specified exact-rank strata and persist while the same pencil encodes an independent ordinary tensor-isomorphism problem. |
| [Recovery from the unmarked scheme](Recovery.md) | When $\dim T<m(m-1)/2$ the abstract first rank-drop scheme determines $T$ up to isomorphism, including any nilpotents. The proof also describes the automorphism functor. |
| [Polarized Artinian deformations](Deformations.md) | Consecutive polarizations recover the scheme and the ordinary raw tensor transporters. Unmarked pencil transporters recover the auxiliary polarization. A special-fiber marking gives recovery of the original ample line bundle in the general Artinian deformation construction. |
| [Exact counting and arithmetic](Counting.md) | Counting pure first-rank-drop points is parsimoniously $\#\mathrm P$-complete over every fixed finite field, also for closed points of each fixed degree. The proof gives explicit zeta factors and an algorithm exponential only in the number of independent quadratic equations for a fixed field. |

The four main proofs are in prose and include exact finite controls. An independent Lean kernel and transitive-axiom audit verified the rank-gap arithmetic in [RankWindows.lean](RankWindows.lean). Priority for the exact statements remains unconfirmed. Prepared for MathProofs with AI assistance.
