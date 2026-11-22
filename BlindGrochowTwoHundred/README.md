# Two hundred universal results from structural proof search

The four workers selected 720 different multi-input matches from a packed bank of 590,787 Lean declarations, with filters based on numeric expression records. Each received 180 potential starting points. After revealing names, the workers developed universal results in four areas. Each route contributes 50 selected proofs.

| Route | Results |
|---|---|
| A | Matched extension suites, exact signed-weight thresholds, and recovery from weighted observations |
| B | Exact determinant ranges from support components, character constraints, and matrix transport |
| C | Normal forms for algebra isotopy, reconstruction from contractions, and volume constraints on tensor actions |
| D | Greedy rank-test selection, exact weighted erasure costs, and dimension-loss formulas |

## Lead statements

- **Matched extension suites.** A matched suite of cycle-power observations recovers the cycle period at the gcd of the suite exponents. The recovery criterion accounts for a known bound on permitted lengths. The proof package also studies when marginal tests and modular counts lose information. [A](A.md)
- **Determinant ranges from support components.** With jointly separating diagonal anchors, a transporter for a diagonally twisted matrix tuple has one free scalar per support component. The attainable determinants are the product of the twist and independent powers with exponents equal to the component sizes. Over a finite field these exponents yield a single gcd formula for the determinant coset. [B](B.md)
- **Algebra and form transport.** The same algebra can admit different transports depending on restrictions on the input and output maps. The exact normal forms recover permissible transports and track determinants, including when further contraction information forces a common algebra equivalence. [C](C.md)
- **Durable rank tests.** A prescribed finite family of subspaces can be covered by a short list of seeds whenever a uniform fraction of seeds preserves rank on each subspace. The proof controls the residual after each greedy step. With weighted erasures, the full union of successful seed fibers measures the cost of disabling any specified target set. [D](D.md)

The algebra and Frobenius results also give an exact count of determinant-one orbits inside the ordinary orbit of a finite étale multiplication tensor. The count has a written proof using the formal determinant-fiber theorem. [Orbit count](Synthesis.md)

## Audit and reproducibility

The published count concerns 200 universally quantified declarations. The worker notes identify the strongest conclusions and state their hypotheses, applications and precedents. Some results develop related consequences of the same proof method. The exact statement and proof of every selected result are in the Lean files. [Theorem index](Theorems.md) · [Audit](Audit.json)

The frozen queues used seed 64403593 on the shared packed snapshot. The public verifier accepts a compatible Lean and Mathlib installation and an independent source-and-axiom checker.

~~~text
python proof_pass.py plan BANK queues-copy --seed 64403593 --keep 180 --quotas 50 50 50 50
python fanin.py BANK --reveal queues-copy/worker-1.json
python proof_pass.py audit Pass.json CHECKER receipts --target 200
~~~

[Frozen queue A](queues/worker-1.json) · [Frozen queue B](queues/worker-2.json) · [Frozen queue C](queues/worker-3.json) · [Frozen queue D](queues/worker-4.json) · [Pass manifest](Pass.json)

The target problems connect to isomorphism of tensors, algebras and matrix tuples under the given structural hypotheses. [Grochow and Qiao on TI-completeness](https://arxiv.org/abs/1907.00309)
