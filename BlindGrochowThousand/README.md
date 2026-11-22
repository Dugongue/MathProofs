# One thousand checked leads for structured isomorphism tests

Four workers each developed a reproducible search and a 250-proof batch. Numeric input and output expression IDs in a packed Lean library nominated 800 disjoint candidates before any names were revealed. The workers used those candidates to choose representations and finite search spaces after reveal. Their generators then tried concrete inputs and proposed statements. Lean independently checked the resulting proofs.

| Worker | Proofs | Search |
|---|---:|---|
| A | 250 | Cycle profiles and collision thresholds for Frobenius observations |
| B | 250 | Determinants of simultaneous transporters for anchored matrix tuples |
| C | 250 | Ordinary and common-basis equivalence for weighted trilinear forms |
| D | 250 | Exact rank-preservation spectra for binary projection panels |

## How to use the results

The audited count comprises 999 concrete certificates and one theorem over arbitrary fields in the matrix batch. Several additional universal verification rules are proved in the sources. The worker notes describe the finite universes and which computations answer a classification question. The theorem index gives all target names. The audit gives the exact count, source hashes and transitive axioms for the retained proofs. A concrete theorem can give a counterexample, a valid design, or a fully checked observation on a finite family. Results explicitly quantified over a family are identified separately in each worker note. The scripts supply candidate statements and the Lean audit supplies proof evidence. [A](A.md) · [B](B.md) · [C](C.md) · [D](D.md) · [Theorem index](Theorems.md) · [Audit](Audit.json)

The previous 100-proof pass developed reusable lemmas by hand. This pass uses four generators and treats mathematical variety as a choice of search space and equivalence filters. For example, the binary panel search rejects repeated rank-preservation spectra within a dimension. A change of basis preserves that spectrum. The proposed examples can seed subsequent theorem discovery, including finding which finite classifications have uniform explanations.

## Reproduce

The structural input is a packed bank of 590,787 declarations with 823 qualifying multi-input matches. The freeze used seed 7253119. Each worker's frozen queue contains 200 matches. Proof checking used Lean 4.33.0 and the matching Mathlib environment. There are no native-evaluation axioms in the audit.

~~~text
python proof_pass.py plan BANK queues-copy --seed 7253119 --keep 200 --quotas 250 250 250 250
python fanin.py BANK --reveal queues-copy/worker-1.json
python A-gen.py
python B-gen.py
python C-gen.py
python D-gen.py .
python proof_pass.py audit Pass.json CHECKER receipts --target 1000
~~~

[Queue A](queues/worker-1.json) · [Queue B](queues/worker-2.json) · [Queue C](queues/worker-3.json) · [Queue D](queues/worker-4.json) · [Pass manifest](Pass.json)

The matrix-tuple and common-basis examples are special presentations of transport problems studied in tensor-isomorphism complexity. The binary tests are finite rank-condensation experiments. [Grochow–Qiao](https://arxiv.org/abs/1907.00309) · [Forbes–Guruswami](https://arxiv.org/abs/1411.7455)
