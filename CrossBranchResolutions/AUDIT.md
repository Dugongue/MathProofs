# Scope and evidence audit

## Mathematical outcomes

The Hanner proof was checked independently by four workers. The checks covered first and second derivatives, both angular integration-by-parts formulas, the positive-semidefinite Gram matrices, invertibility of the Hessian rescaling, the epsilon limit, zero coordinates, arbitrary complex phases, integrability and Jensen's inequality. The resulting statement matches the full Steinhaus missing-range question, for every finite number of functions. It does not resolve the Rademacher or Schatten variants.

The Jonsson counterexample was checked independently for the exact direction of the J-preorder, connectedness, unital bimodule actions, the index-15 separability element, the central-idempotent restriction and the Loewy-length comparison. Its tensor-power extension retains connectedness and yields lengths 4r+1 and 2r+1. The principal-block value 5 is established literature, not a new discovery.

## Computational checks

The A5 checker uses binary linear algebra and explicit arithmetic in F4. Its 3,600 representation-product checks, rank calculation, radical-power dimensions, central idempotent, corner-center calculation and subgroup projection are exact. The computed radical-power dimensions are 60,35,27,17,9,0. It also records a nonzero product of four radical elements. These computations were rerun independently; they are not Lean-kernel verification.

The Hanner diagnostic compares the direct regularized Hessian with the Gram formula in 12 deterministic quadrature cases. The maximum entrywise residual was below 7e-15 on this run. This is a consistency check, not a certified error bound or a proof over all inputs. The analytic proof supplies the universal result.

## Relationship to the structural scan

The earlier structural scan yielded 104 import-incomparable candidate representatives. They were divided into 27 algebra, 41 analysis, 10 discrete and 26 category-theory cases. The direct joins mostly transport existing hypotheses or compose standard lemmas. No new theorem follows just from a miner score or an import-graph edge.

The analysis follow-up moved from convexity/Jensen interfaces to the stated Hanner question and derived a new explicit Hessian argument. The algebra/discrete follow-up compared the radical/separability neighborhood with modular block theory, exposing the Loewy-length counterexample. These are manually developed mathematical consequences of following the candidate neighborhoods, not automatically generated Lean proofs. The remaining candidates produced no additional claimed open-problem closure in this run.

## Primary sources and priority

- Jonathan Jenkins and Tomasz Tkocz, [Complex Hanner's inequality for many functions](https://arxiv.org/html/2207.09122v2), Lemma 2 and Section 3.2: the convexity reduction and the missing Steinhaus range.
- Helena Jonsson, [J-equivalence for associative algebras](https://doi.org/10.1007/s13366-024-00757-8), Definition 1 and Conjecture 43: the connected-algebra preorder and proposed Loewy-length monotonicity.
- Charles W. Eaton and Michael Livesey, [Loewy lengths of blocks with abelian defect groups](https://arxiv.org/pdf/1607.08795), Introduction, page 1: the principal characteristic-2 block of A5 has Loewy length 5.
- Jakimiuk, Tang and Tkocz, [Khinchin inequalities for uniforms on spheres with a deficit](https://arxiv.org/abs/2506.22040): a nearby follow-up considered during novelty checking; its conclusions must not be conflated with the missing Hanner reversal.

Searches covered the exact conjecture names, author names with correction/counterexample, Steinhaus convexity, angular/Hessian methods, and recent arXiv, GitHub and Hexagon results. No earlier explicit closure was located. This bounded search does not establish first discovery. The new Hanner proof and the observation contradicting Jonsson's conjecture should receive specialist review before any claim of publication priority.

## Verification status

Both main documents contain complete informal arguments. No Lean proof, axiom audit or checked DAG port is claimed for them. Source-catalog inclusion, if present, is discovery metadata only. The numerical and exact computational evidence have the separate scopes stated above.
