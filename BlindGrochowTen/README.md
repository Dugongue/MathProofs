# Ten Lean proofs from a four-worker structural search

The four workers used a common packed Lean bank with 590,787 declarations. The selector matched numeric input and output expression IDs before opening declaration names. Each worker froze a separate seeded shortlist. The four lists retained 850 entries with 501 distinct consumers. The search nominated structures, and the workers developed and reviewed the mathematical statements after seeing them.

## Results

| Route | Independently audited conclusions |
|---|---|
| A | Recover a cycle profile from noisy divisor marks. Recover it even after polynomial amplification of those marks. Recover it from two Frobenius decks if the graph of allowed periods is a forest. |
| B | Explicit quadratic trace certificate for a transported word. Equal dimensions in the split-image conjugacy test. Existence and uniqueness of a pointed simultaneous conjugator from transition coordinates on bases of words. |
| C | Full normal form for isotopy of multiplication in unital associative semiring algebras. Classification of weighted trace trilinear forms by algebra equivalence and a cube-class condition. |
| D | Exact first dimension of collision with a missing fixed-point count on prime-power profiles. Complete reconstruction of those profiles from the nullities of a short sequence of matrix powers. |

The strongest lead for tensor isomorphism is the forest test. Fix the permitted list of degrees of the field factors. The quadratic and cubic extension observations jointly classify the finite étale tensor orbit on that support exactly when the bipartite multigraph of the resulting orbit lengths has no cycle. The Lean theorem proves recovery from the leaf condition. The written proof gives the graph criterion, its converse and a linear-time reconstruction from the decks. [Frobenius recovery](A-Proofs.md)

For matrix proof complexity, the exact degree-two criterion for arbitrary labelled tuples has a written proof. The linear space of all intertwiners either satisfies a compatibility test for mixed moments, or supplies a pair of constant matrices whose traces differ and that yields a quadratic certificate. Lean checks the explicit certificate identity. The existing sharp characteristic-zero degree-three result for single matrices is prior project work. [Matrix proofs](B.md) · [Galesi, Grochow, Pitassi and She](https://arxiv.org/html/2305.19320#S7.SS3)

The trace-form classification applies also in characteristics 2 and 3 when the target trace pairing is nondegenerate. The account credits Harrison and Pareigis for the finite separable field case in characteristics prime to the degree factorial. The prime-power results formalize finite formulas for cycle profiles, with the permutation interpretation and field-independence argument given in prose. [Algebra transporters](C.md) · [Power marks and nullities](D-Proofs.md)

## Repeat the pass

The reusable planner takes one numeric snapshot and distributes a single frozen shortlist to four disjoint queues, with quotas of 3, 3, 2 and 2. The default pool is 128 candidates per worker. The planner itself opens no declaration names. After freezing, reveal individual queues with the structural selector.

~~~text
python proof_pass.py plan BANK next-pass --seed 395765
python fanin.py BANK --reveal next-pass/worker-1.json
python proof_pass.py audit Pass.json CHECKER new-receipts
~~~

Develop the best candidates and keep alternatives available if a statement fails or duplicates known work. Record the ten reviewed claim IDs in the pass manifest. The audit command runs the workspace Lean checker serially, checks source hashes, and exits unsuccessfully if a batch fails or the ten-proof target is missed. It rejects duplicate claim IDs, theorem names and source paths. Mathematical overlap is reviewed when assigning the IDs. The checker expects a compatible Lean installation and Mathlib. The four queues organize synthesis across workers. Formal proof construction and selection remain researcher-directed.

[Pass manifest](Pass.json) · [Kernel and axiom audit](Audit.json) · [Planner and verifier](proof_pass.py) · [Blind selector](fanin.py)

## Recorded inputs

The tables below are the freezes for this research run. A separate replay exercised the new disjoint planner. The selected theorems and their priority claims have the scopes stated in the individual notes.

| Route | Frozen data |
|---|---|
| A | [Finite-support Frobenius](A-Frozen.json) |
| B | [Matrix conjugacy](B-Frozen.json) |
| C | [Algebra transporters](C-Frozen.json) |
| D | [Power marks and nullities](D-Frozen.json) |
