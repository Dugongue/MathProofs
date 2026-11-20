# Navier–Stokes methods for the ternary TI and SL-TI comparison

The target is a deterministic same-field polynomial-time many-one reduction from full determinant-one three-tensor isomorphism to ordinary three-tensor isomorphism over $\mathbb F_3$. Write $P_j$ for the decision problem with $j$ specified determinant-one conditions on one common transporter. One ordinary orbit can split into four $P_2$ classes. The unrestricted reverse reductions between the four tiers remain open here. [Open Question 1.9](https://arxiv.org/html/2306.03135v2#S1.SS5)

## Exact results inside the four-class case

- **Fifth Fourier moment.** A split Pfaffian and a small relation width give a numerical sign readout when the fifth correlation is nonzero. It removes both matrix signs on the same raw transporter and sends $P_3$ to $P_1$. An explicit family with dimensions $(28+4k,28+4k,8+k)$ for even $k$, scalar pair adjoints and zero mean has exactly four $P_2$ classes in every ordinary orbit. The remaining label sign is freely correctable, giving one ordinary TI instance for full $P_3$. [Proof](FifthMomentSigns.md)
- **Held action tensor.** A projective corner and the parity of radical multiplicities give exact calibration on a recognizable ordinary-TI-complete action-tensor family with exactly four $P_2$ classes per ordinary orbit. The general recognition conditions also give $P_3$ to $P_1$ on a broader class of filtered action tensors. [Proof](HeldActionSignProfiles.md) · [Nonsplit extension](NonsplitParityAppendix.md)

## Further reductions

- **Pfaffian relation spaces.** The first harmonic average removes two linked matrix signs when its value is nonzero. A polynomial bank of colored relation tuples enforces the same two signs even when an odd automorphism forces all such scalar moments to vanish. A complete projective relation space puts all three signs under one small exterior-algebra mark and gives one ordinary TI instance. [Average](PfaffianHarmonicReadout.md) · [Colored tuples](PfaffianRelationColors.md) · [Complete projective case](CompleteProjectiveRelations.md)
- **Low-rank cut trees.** Signed-tree front assembly computes a determinant character sum on either the slice span or its trace annihilator. A nonzero sum reads the product of the two matrix signs and permits one two-sign comparison. The theorem handles large dimensions and neutral fixed-mode determinant corrections when the stated coupling and label-cut widths are available in the given matrix coordinates. [Proof](FourierCutTree.md)

These papers use the pinned Navier–Stokes phase projection, signed-tree assembly, and held adjoint correction. Each note proves the full reduction on its stated family and gives its own recoverability and complexity conditions. The examples attaining four classes instantiate the bottleneck without proving a collapse of the unrestricted tiers. [Navier–Stokes Lean source](https://github.com/tristanbuckmaster/navier-stokes/tree/ad53419de079eb8f95f60313473374624a348546/lean)

## Verification

The reduction proofs are written mathematics. The three Lean companions cover fifth-correlation transport, ternary Fourier weights, and exact sign recovery from projected cosets. Their exact hashes and transitive axiom sets are in [Verification.json](Verification.json). Separate exact finite scripts check the numerical moment seed, the scalar-adjoint pencil, Fourier duality, the cut-tree merge, projective sign calibrations, and the held-action signs.
