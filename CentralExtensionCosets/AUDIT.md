# Audit of central-extension cosets

**Status:** informal mathematical derivation and finite computational controls. No independent peer review, Lean certificate, full algorithm implementation, or established publication priority is claimed.

## Exact scope

Theorem A searches a supplied coset of quotient isomorphisms whose source group lies in a fixed bounded-composition-factor class. Kernels must be central. It returns witnesses, full coset generators and exact counts in polynomial Cayley-table time. Theorem B computes its own center, quotient decomposition, initial quotient map and solvable subgroup from raw class-two group tables. Its cost is polynomial times the product of complete-flag counts for repeated equal-order cyclic summands of the central quotient. It is polynomial under bounded multiplicities, not for unrestricted class-two groups.

## Critical checks

1. The finite-ring orbit lemma uses left multiplication consistently. The equation $ba+c=1$ gives a unit of the form $a+tc$, so its value on $x$ is exactly $ax$. No search for a unit is charged as a polynomial subroutine.
2. Coefficient endomorphisms act on cohomology and commute with quotient pullback because the kernel action is trivial. This step does not assert the same result for arbitrary noncentral kernels.
3. The generated subgroup is represented in cyclic coordinates; the exponentially large cohomology group is never enumerated.
4. Subgroup images modulo $pB$ and intersections with $pB$ do not determine a subgroup. The residual homomorphic section is retained and compared by an affine action on $\operatorname{Hom}(D,(pB/W)[p])$. The explicit example inside $(C_4)^2$ in the tests catches omission of this step.
5. The recursion has a single recursive call at each exponent level. Generator actions are retained as matrices and polynomial-size straight-line programs, avoiding expanded words. Every stage has size bounded by a polynomial in the original input.
6. Luks–Miyazaki Proposition 3.17 supplies the exact vector and subspace transporter operations used here. Its polynomial dependence on field size is allowed for Cayley-table inputs; no polynomial-in-log-prime claim is made.
7. The nilpotent kernel in the endomorphism ring is proved by its action on the quotient modulo $p$. Its unit group is generated using all levels of the nilpotent filtration, rather than assuming additive generators of the first level alone suffice.
8. All quotient maps are covered by the computed flag transversal. An arbitrary isomorphism preserves the full center, so there is no supplied characteristic-subgroup assumption in Theorem B.
9. Arbitrary lifts of quotient stabilizer generators, together with the full fixed-quotient kernel, generate the entire automorphism group. The fixed-map search and marked-search dependency is reproduced in the companion proof.

## Reproducible finite checks

Run `python check_small.py`. The saved results contain 593 unit-orbit comparisons, 61 pairs of complements, 1,922 affine-action checks, and six full small abelian automorphism-group controls. All passed. Tests enumerate small objects and are not the polynomial transporter algorithm. They do not prove the general theorem or its runtime.

## Sources and novelty

- [Grochow–Qiao, Algorithms for Group Isomorphism via Group Extensions and Cohomology](https://arxiv.org/abs/1309.1776): extension framework and relevant open questions. The unrestricted abelian-radical question remains open in this manuscript.
- [Luks–Miyazaki, Polynomial-time normalizers](https://ix.cs.uoregon.edu/~luks/polytimenormalizers.pdf): Proposition 3.17, the principal algorithmic ingredient.
- [Ciocănea-Teodorescu, Algorithms for finite rings](https://arxiv.org/abs/1512.08365): finite-module isomorphism used in the companion fixed-map proof.
- [Skresanov, Polynomial-time isomorphism test for k-generated extensions of abelian groups](https://arxiv.org/abs/2602.15497): recent comparison for kernel lifting.
- [Faster Isomorphism for Groups of Class 2](https://arxiv.org/abs/2611.05920): recent unrestricted bound, not superseded by the present parameterized bound.

Searches included central-extension algorithms, solvable quotient automorphism groups, subgroup transport in finite abelian groups, and multiplicities in abelian quotients. They did not establish priority for the combined theorem. Older composition-series algorithms and implicit consequences of existing transporter methods remain important novelty comparisons. The appropriate description is a concrete informal theorem for expert assessment, not an announced record or closure of unrestricted Group Isomorphism or TI versus SL-TI.

The DAG supplied source-level pointers to augmentation modules, Jacobson radicals and nilpotent-unit lemmas. These are classical supporting ingredients. Finding their declarations in a catalog is not a kernel verification of this manuscript or evidence that those ingredients are new.

No third-party source code is reproduced. Mathematical arguments and citations are presented with attribution; the companion manuscript and finite checks are project-authored.
