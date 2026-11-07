# Arithmetic and geometric universality at rank two

[Full informal proof](PROOF.md).

For every affine scheme X of finite type over the rationals, the construction gives a binary partial matrix whose anchored rank-two completion scheme is isomorphic to a principal open subset of X times affine space, with a smooth surjection onto X and nonempty fibers over every characteristic-zero field-valued point. This preserves singularity types up to smooth variables and rational-point existence.

Combining the construction with explicit local witnesses and rational-point smoothing gives a computable equivalence with Hilbert's tenth problem over the rationals even when the completion scheme is smooth and geometrically integral and has points over the reals and every p-adic field. The smoothing step has no claimed polynomial-time bound. Undecidability is conditional on a negative answer to Hilbert's tenth problem over the rationals; the geometric theorem and equivalences are unconditional informal claims.

This document upgrades the earlier decision reduction by tracking coordinate rings, rather than assuming that equal solvability implies equivalent solution spaces. It does not assert identical topology or use tensor-isomorphism orbit reductions as completion reductions.

Status: informal author audit; no independent review of the new geometric strengthening, no Lean certificate, and no certified publication priority. The antecedent rank-two gadgets had internal reviews and bounded finite checks. Shitov's earlier matrix-completion and nonnegative-factorization universality results are credited in the proof. No upstream source code is included.
