Sharp universal incompatibility of three four-outcome quantum measurements

RESULT
Every triple of four-outcome POVMs in every finite complex dimension admits a normalized positive joint parent whose marginals dominate η* times the original effects, where

    η* = (1 + cos(π/9))/3 = 0.6465642069286361...

The bound is sharp: the previously published dimension-8, rank-2 Hadamard–Clifford triple attains equality. The universal SOS hierarchy already attains the exact value at level 3.

STATUS
Computer-assisted informal proof. Exact rational algebra in Q(c), c = cos(π/9), verifies all polynomial identities. Rigorous outward-rounded interval arithmetic verifies positive Gram matrices. Independent workers checked the full uncollapsed identity and a separate rational-congruence/Gershgorin positivity certificate. No Lean formalization or external human peer review is claimed.

READ
PROOF.txt gives the readable proof assembly; proof.tex contains the theorem, explicit parent construction, proof of universal marginal domination, common POVM dilation, sharpness and attribution. FourOutcomeTriple_UniversalSOSCertificate.json is the exact finite witness. Its matrices are part of the proof, not numerical solver output.

REPLAY
Use Python 3.10 or newer in a normal local environment:

    python -m pip install -r requirements.txt
    python verify.py
    python verify_whitening.py
    python check_sharpness.py

No optimization solver, Julia, NumPy, SciPy, GPU, network connection, Lean installation or saved SDP checkpoint is needed to replay after installing the stated dependency. Do not use Python -O: the checkers use assertions and explicitly reject optimization mode.

Frozen verification receipts are included. verify.py and verify_whitening.py write a new receipt only when given --receipt PATH; check_sharpness.py preserves a matching existing receipt. Discovery scripts and their dependencies are preserved in the parent research directory; they are not needed for replay.

CREDIT
Sébastien Designolle and Máté Farkas supplied the conjecture, sharp Hadamard–Clifford construction, spectral value and numerical evidence in arXiv:2609.20728v1. Sébastien Designolle supplied the universal SOS framework. Our prior pairwise-unbiased parent and operator-defect formalizations informed the contact-polynomial search. The new contribution here is an exact universal degree-6 parent/marginal certificate and its rigorous verification, covering arbitrary measurements without unbiasedness assumptions.

https://arxiv.org/html/2609.20728v1
https://github.com/sebastiendesignolle/arXiv-2609.20728
https://arxiv.org/abs/2509.10381

Scope: this settles the (k,n) = (3,4) instance, including level-3 attainment. It does not establish the all-parameter convergence conjecture. Literature searching found no independent exact solution, but exhaustive priority verification remains separate from this proof.
