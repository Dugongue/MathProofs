# Four advances in permutation-group conjugator search

The starting point is the conjugator-search reduction for affine constituents with abelian local complements. The new marking construction works for arbitrary small quotients and pins a partial map simultaneously up to a single inner automorphism.

| Result | Scope |
|---|---|
| [A polynomial-degree rigidifier for every finite quotient](quotient-marker.md) | Given a finite group's multiplication table, construct a faithful permutation extension of degree \(O(m\log(m+1))\) on three orbits, where \(m\) is the quotient order. The construction also has an unmarked form. The induced quotient automorphisms are exactly the inner automorphisms. |
| [Search and full normalizers for polynomial-order permutation groups](polynomial-order.md) | Uncoloured permutation-group conjugacy decision suffices for a conjugator, full normalizer generators, and the exact number of conjugators, on arbitrary actions of groups of order polynomial in the degree. |
| [Conjugator search with nonabelian affine quotients](affine-blocks.md) | Search reduces to uncoloured conjugacy decision for regular abelian constituents with polynomial-size quotient blocks and surjectivity onto the product of the block quotients modulo their centers. This includes arbitrary coupling of simple complements in diagonal blocks and an unrestricted number of abelian constituent factors. |
| [Full affine normalizers and exact counting](affine-normalizers.md) | On the affine class, a conjugacy oracle gives full normalizer generators, conjugator cosets, exact counts, and an exact uniform sampler. The fully pinned kernel has a deterministic algorithm without oracle queries. |

The four main theorems have written proofs. The [Lean source](AffineConjugacyAdvances.lean) and [audit](Verification.json) cover the Cayley-marker implication, the graph conjugation identity, and terminal normalization.
