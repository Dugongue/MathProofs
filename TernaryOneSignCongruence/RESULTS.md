# Ternary one-sign congruence and the square-zero normal form

## Exact reduction for arbitrary inputs

Every one-sign alternating-space instance over $\mathbb F_3$ reduces in deterministic polynomial time to a pair with a pure-power Pfaffian, a known matchable nonsingular form, and a commutative local ratio algebra with square-zero radical. For equal formats it preserves the entire set of attainable signs. After aligning the known forms, the ambient congruence is symplectic and the entire requested sign is the determinant of its actual action on the radical of the ratio algebra. The theorem includes inputs with identically zero Pfaffian. This gives one recognizable family sufficient for the full ternary TI versus TI_SL question. [Normal-form proof](SquareZeroNormalForm.md) · [Published question](https://arxiv.org/html/2306.03135v2#S1.SS5)

The required ordinary TI encoding of the sign for every represented square-zero radical remains open. In particular, the original alternating space is still encoded in how the radical acts on its symplectic module. Abstract automorphisms of the square-zero algebra alone do not give the allowed sign corrections. Its trace Gram form vanishes on the radical, and its single linear Pfaffian factor supplies only a rank-one quadratic on the label space.

## Exact ordinary TI reductions on wider families

- [Local pencils](LocalPencil.md) use the residue, cotangent and socle of the ratio algebra. Truncated polynomial algebras permit arbitrary cotangent rank when its determinant exponent is even. A graded Gorenstein version permits arbitrary width for odd socle degree or even residue extension degree.
- [Casimir centralizers](CyclicCasimir.md) use checked conjugation covariants and a paired invertible anchor. The common centralizer flag reduces even a large space of forms to norms on its exterior-square grades. This allows commutative centralizers or the stated small simple-rank condition.
- [Factor-derived anchors](FactorWordAnchorBank.md) give polynomial raw matching from bounded-degree factors, with no logarithmic bound on the simultaneous commutant. The maximal-Pfaffian-minor extension includes always-singular spaces of fixed generic corank.
- [Singular Casimir composition](SingularCasimirComposition.md) combines the fixed-corank factor marks with the quotient Casimir and annihilator determinant. It applies without a small label radical when the stated module-rank tests pass.
- [Split-label parity](SplitLabelParity.md) cancels the norm multipliers and retains only geometric label permutation sign for independent split Pfaffians. Arbitrary factor multiplicities give a polynomial Turing reduction. Bounded label bases or logarithmic multiplicities give one ordinary TI instance.

The reduction proofs are written mathematics and the normal form was reviewed independently. The two Lean companions certify the square-zero shear identities and the positive inversion-parity formula when the chosen marks determine the label map. The audits cover those named lemmas. The Casimir proof also reuses the existing Lean covariance declarations. [Verification](Verification.json)
