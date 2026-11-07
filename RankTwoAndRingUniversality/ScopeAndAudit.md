# Scope and audit record

## Verification status

All four mathematical proof documents are informal. Internal reviewers checked the constructions in both directions and their polynomial size. No Lean source, compiled certificate, or independent external review is claimed.

The included Python script was executed successfully. Its output was:

```text
17 scalar-copy, 578 gate, 2953 coloring-pair checks passed over F2/F3/F5/F7
All checked explicit partial matrices used only pinned 0/1 and no duplicate prescribed coordinates.
```

The scalar-copy check includes zero to test rejection. Gate checks include repeated operands. The finite checks do not establish the general theorem; the coordinate-forcing proof and the nonzero-arithmetic conversion supply that argument.

## Central mathematical checks

For matrix completion, the pinned identity matrix fixes the factor coordinates. Every equation in a gadget is an individual specified entry, with no shared-placeholder convention. Nonzero source variables are produced by an explicit conversion of general field equations. Small finite fields use an independent projective-line coloring reduction. Specified entries are binary; completed entries need not be binary or nonnegative.

The PSD corollary uses a Gram factorization of the rectangular completion, with both diagonal blocks free. Its symmetric-completion variant pins a positive identity principal block. Neither claims hardness for the fully unit-diagonal binary problem.

For the ring compiler, the off-diagonal ideal is recovered as the commutator ideal. Free corners in its square quotient identify the labels after reduction to every residue field. Two unique tags pin each original vertex even after taking the opposite-algebra fiber product. Idempotent lifts are simultaneously conjugated using a unit congruent to one modulo the nilpotent ideal. Monic terminal relations preserve freeness. The commutative-algebra step eliminates scalar leakage by same-half zero products rather than assuming a distinguished augmentation. The final centroid calculation uses mixed typed pairings and never divides by two or three.

For the smaller form reduction, the symmetric power is treated as a quotient in every characteristic. Independent upper-block shears realize the full kernel of this quotient. This is not an assertion that averaging by a factorial is available in small characteristic.

## Existing results not counted as new closures

Shitov's rank-three completion theorem already supplies the broad ordinary-completion and constant-rank conclusions printed as questions in Compendium A16. Complex unitary tensor containment by adjoining the conjugate tensor was already proved by Lysikov and Walter; it is not a new result here. General affine rank-minimization hardness and the general constrained-invertibility problem also have prior results and are not claimed as discoveries in this package.

The ring theorem extends the finite-free setting of the cited ring comparison theorem. No universal special-linear-to-ordinary-TI reduction follows from these arguments. The smaller form-size theorem is not advertised as a runtime record. Four statements in the overview should not be counted as four independent longstanding open problems.

## Library use

The federated library search included symmetric-algebra and quotient constructions, including the [AxiomMath Stacks source tree](https://github.com/AxiomMath/Stacks). Retrieved source declarations are discovery evidence, not a kernel certificate for these results. The proof documents give the arguments themselves and do not require accepting an unverified library statement as a missing step.

## Publication handling

Only the proof notes, this scope record, the overview, and the bounded-check script belong to the publication payload. Local operational logs, indexing records, credentials, and machine paths are excluded. The upload procedure preserves unrelated README content and uses a generic author and committer identity.
