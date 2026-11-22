# Four extensions of the Ceva determinant compiler

These results start with the exact determinant character of graph-indexed tensor-isomorphism tests. They use it to recover hidden component structure, optimize witnesses, lift corrections through quotients, and implement conditional linear characters.

| Result | Main conclusion |
|---|---|
| [Stabilizer counts recover a matroid rank](A.md) | Ratios of counts for equal-rank multiplication algebras recover the rank of selected pins after contracting failed TI components. Three nonadaptive determinant-one stabilizer counts suffice to count arbitrary raw TI transporters over a fixed finite local ring with nontrivial units. |
| [A prime-sensitive witness-cost problem](B.md) | With the ordinary edge statuses known, the minimum correction cost is a modular cut optimum. One active prime gives a deterministic exact algorithm. Two prime-modulus tests have a randomized polynomial-time exact algorithm. Three active primes already give NP-completeness over $\mathbb F_{31}$ with identity witnesses. |
| [A Segre grid implements linear span programs](D.md) | Realizes conditional monomial equations and exact determinant images on the same finite local ring. It gives all thresholds and represented matroid tests, together with a size separation from terminal connectivity on freely varying yes/no bits. |
| [Precision lifting has cycle obstructions](C.md) | Exact higher-precision axis-action fibers include a character constraint and a fundamental-cycle constraint. Every individual side can lift while the triangle fails to lift. |

The full arguments are written proofs, with Lean checks of component identities and separate finite controls. [Earlier Ceva compiler](https://github.com/Dugongue/MathProofs/blob/main/PolyhedralTensorDeterminants/A.md) · [Audit](Audit.json)
