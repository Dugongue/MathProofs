# Review and Prior Art Scope

This accompanies [Fixed Characteristic Field Independence for Tensor Isomorphism](Proof.md), dated 31 October 2026.

## Exact mathematical claim

For each **fixed** prime $p$, ordinary three-tensor isomorphism over $\mathbb F_{p^s}$ and $\mathbb F_{p^t}$ are equivalent under deterministic polynomial-time many-one reductions. The field degrees may vary under supplied standard polynomial presentations. The polynomial may depend on $p$.

This is the finite same-characteristic clause of [Grochow and Qiao's published Open Question 7.6](https://epubs.siam.org/eprint/VA7M2DT6DFQMVDVWIBBN/full), numbered 10.6 in the longer arXiv version. The different-characteristic and finite-field-versus-rational clauses are outside the conclusion.

## Internal review

Four AI workers carried out separated tasks: adversarial mathematical review, published compiler and complexity review, prior-art review, and proof assembly with scope checks. The compiler reviewer also authored the earlier construction; that review is therefore a source and complexity check rather than independent mathematical-author validation. The separate adversarial reviewer re-derived the mathematical implications. This process is internal AI-assisted checking, not external peer review or formal verification.

The checks cover:

- Covariant tensor equivalence versus bilinear-map equivalence before scalar restriction.
- Symmetric-algebra multiplication in characteristic $p$, including repeated input sorts and no division by factorials.
- The basis-linear pure-power inclusion, identity link, prime-field fixed points, invertibility, and exact source-field centralizers.
- Both directions of the encoded isomorphism equivalence for every tensor.
- Published FGS applicability with $3p+3$ space sorts and $3p+7$ tensor components.
- Fixed-$p$ polynomial size, supplied field presentations, and zero or mismatched format handling.

Fresh finite controls additionally checked every $2\times2$ matrix over $\mathbb F_4$ and $\mathbb F_9$, mixed symmetric monomials, the identity link, source-field centralizers, and 41,904 small scalar-transporter triples including zero tensors. These controls support specific interfaces; the general proof is the mathematical argument in the note.

The exact reviewed proof-file SHA-256 is:

```text
3c0f06e993c561d37e75e19613526c878d4fab5d082a79347689428a8fd8be81
```

The result is an informal theorem with internal reviews. There is no Lean certificate or claim of external validation in this bundle.

## Novelty review

The bounded search did **not locate an earlier primary statement of this exact compiled same-characteristic comparison**. That does not establish novelty or priority. Unindexed, differently named, unpublished, private, or recently posted work can be missed.

The source-extension-to-prime-field direction is already a straightforward restriction-of-scalars and centralizer consequence of published tensor-system compilation. The equality additionally uses the classical Frobenius inclusion and an identity link to force transporter entries into the prime field. The note presents this as an explicit assembly of established mathematics and gives its full complexity accounting.

Primary sources examined for the question and its ingredients include:

- [Grochow–Qiao, TI-completeness](https://doi.org/10.1137/21M1441110), especially Theorem 7.3 and Open Question 7.6.
- [Futorny–Grochow–Sergeichuk, Wildness for tensors](https://arxiv.org/abs/1810.09219), especially Theorem 1.1, Remark 1.1, and the repeated-support and variance conventions.
- [Breen–Mikhailov–Touzé, Derived functors of the divided power functors](https://doi.org/10.2140/gt.2016.20.257), Section 3.2.2, pp. 267–268, for the classical pure-power Frobenius inclusion.

Later literature checks covered the relevant scope and field-comparison terminology in [Part III](https://arxiv.org/abs/2306.03135), [Part IV](https://arxiv.org/abs/2306.16317), and [Part V](https://doi.org/10.1145/3717823.3718286) of the tensor-isomorphism reductions series; [2026 average-case TI algorithms](https://arxiv.org/abs/2604.00591); [symmetric finite-field tensor decompositions](https://arxiv.org/abs/2605.12295); and the relevant definitions in [monomial tensor isomorphism work](https://doi.org/10.1007/s10623-024-01375-0). These were bounded inspections, not an exhaustive review of all later literature.

Public GitHub repository metadata, a relevant tensor-isomorphism visualizer README, and the public OpenAI mathematics overview were also checked. This was not authenticated whole-GitHub code search and does not establish absence of prior work.

## Attribution and redistribution

Grochow and Qiao receive credit for the named question and complexity formulation; Futorny, Grochow and Sergeichuk for compilation; and the cited classical literature for Frobenius representations. The elementary centralizer and symmetric-algebra arguments are written out in the proof.

The bundle contains an authored mathematical exposition. It includes no upstream software, Lean libraries, paper PDFs, or copied proof text. Invoking a published theorem does not claim authorship of that theorem. No first-discovery, exclusive-ownership, or software-license claim is made for the classical ingredients.
