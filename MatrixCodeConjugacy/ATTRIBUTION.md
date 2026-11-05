# Attribution and validation status

This is AI-assisted MathProofs work, supplied as an informal proof candidate.
Independent human review, publication-priority assessment and Lean formalization
remain pending. The accompanying exact computations are finite diagnostics.

The target question, spectral/trace-dual construction and published random-matrix
inputs are credited to Tiange Li, Yinan Li, Youming Qiao, Dacheng Tao and Yingjie
Wang, *On the average-case complexity landscape for Tensor-Isomorphism-complete
problems over finite fields*, arXiv:2604.00591v2 (November 3, 2026):
https://arxiv.org/html/2604.00591v2

The extension combines trace-orthogonal dimension duality, a polynomial
small-code enumeration cutoff and a dimension-parametric projection-incidence
argument. Prior MathProof density and matrix-code notes are credited in the proof.
The portable finite-field helper is extracted from our prior exact controls;
the checker has been adapted to use only files in this directory and the Python
standard library. No external Lean library or upstream source code is bundled.

To reproduce the finite diagnostics, run `python controls.py` from this directory.
The command rewrites `FINITE-CONTROLS.json`; timing may vary. Successful execution
does not establish the universal theorem or publication priority.
