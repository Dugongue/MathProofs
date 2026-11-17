# Two signs to one: unrestricted reduction audit

The unrestricted deterministic polynomial-time many-one reduction from two-sign tensor isomorphism to one-sign tensor isomorphism over F_3 remains unproved. This packet records an unsuccessful research pass, not an open-problem closure, a complexity separation, or a new theorem claimed to advance the endpoint.

## Exact target

Given explicit dense tensors T and S of the same format, construct in deterministic polynomial time one pair P,Q of explicit dense three-tensors such that

    exists (g1,g2,g3): (g1,g2,g3) T = S, det(g1)=det(g2)=1

if and only if

    exists (h1,h2,h3): (h1,h2,h3) P = Q, det(h1)=1.

All maps are invertible over F_3. The construction receives no transporter, stabilizer generators, invariant flags, orientation oracle, or bound on a tested mode beyond the raw input size. The maps used to satisfy the two source signs must belong to the same transporter. The single target instance must be built without decision-oracle calls.

## What was checked

- [Multiplication networks](PairDependent.md): relative matrices telescope, but imposing a fixed unitriangular affine slice also fixes the endpoint flags. The proposed four-layer compiler excludes some determinant-one matrices. This rejects that proposed compiler, not the reduction.
- [Representations and determinant circuits](Representation.md): a balanced exterior construction gives an exact determinant lock, with exponential auxiliary dimension. The DAG identified this construction in our earlier work, so it is explicitly not a new discovery. Short arithmetic circuits and ordinary tensor-system compilation do not prove the required extension and recovery of the remaining sign.
- [Finite-group and orientation constructions](NewRoute.md): the nonzero-vector permutation action reads determinant exactly, at exponential size. Frobenius relations alone allow both signs; an abstract determinant line does not tie its action to the original transporter.
- [Composition check](Composition.md): the existing neutral conjunction and ordinary-controlled swap constructions still do not implement two independent signed conjuncts. A two-bit truth-table control distinguishes the required conjunction from parity.

The strongest earlier positive constructions retain their exact restrictions. In particular, an ordinary TI conjunct can be absorbed into one signed query, and a logarithmic-dimensional tested mode can be locked using explicit exterior data. This pass did not remove either restriction. No conclusion about impossibility of an unrestricted pair-dependent construction follows.

## Verification and provenance

The proofs and audits are informal, not Lean-certified. Source discovery used the federated DAG front door, including prior project notes and external catalogs; source-only hits were not treated as checked Lean results. The finite controls are regression checks for the displayed finite models, not evidence proving an unrestricted complexity claim. The companion Python script reproduces the two-bit character check and the complete GL_2(F_3) affine-slice check.

For the published ordinary tensor-system compiler see Chen, Grochow, Qiao, Tang and Zhang, [Theorem 4.1](https://arxiv.org/html/2306.03135v2#S4). Its statement does not justify silently preserving a specified physical determinant when replacing a tensor system by one ordinary tensor pair. For the distinction between objectwise and general reductions, see [Fortnow and Grochow](https://arxiv.org/abs/0907.4775) and [Finkelstein and Hescott](https://arxiv.org/abs/1604.08558).

No new publication-priority claim is made. The artifact is retained so that the same failed compiler and rediscovered exterior construction are not presented as fresh progress in a later pass.
