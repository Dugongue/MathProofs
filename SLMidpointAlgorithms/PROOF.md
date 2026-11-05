# Exact midpoint and determinant-coset algorithms for tensor isomorphism

Four informal results from an attack on the fixed-field SL-TI containment problem. The proofs are organized by their mathematical interfaces.

- [Shared triangular completion](ELIMINATION.md) eliminates up to two unspecialized triangular factors by one simultaneous linear system. It gives a branch-free consistency and witness circuit at finite fields, an all-field coefficient test, and a many-one ordinary-TI quotient encoding for one triangular mode with independently controlled remaining modes.
- [Unitriangular midpoint tests](MIDPOINT.md) gives polynomial-time canonicalization, transporter search and stabilizers for a prescribed triangular action. It also gives exact intersection algorithms under an affine-orbit promise or a compatible common unipotent group and subgroup condition.
- [Block-flag determinant cosets](PARABOLIC.md) finds all attainable determinant classes for flag-preserving transporters in time polynomial in the input, the maximum diagonal-block image order and the field characteristic. With width b at fixed q, the bound is polynomial in the input and q^(b²). The proof handles large translation kernels by prime-field linear algebra.
- [One-mode flag reconstruction](ORIENTATION.md) recovers the determinant coset using ordinary-TI decision queries when only one mode has narrow intrinsic flags. It includes scalar-adjoint local-centroid families with all dimensions unbounded.

Together these results discharge conditional shared completion in the arithmetic representation and some exact midpoint cases. The general four-layer reduction still needs an ordinary-TI encoding of the intersection when the two opposing midpoint orbits are unrestricted. No unrestricted Turing or many-one equivalence is claimed.

The methods reuse earlier MathProofs unitriangular controllers, mixed tensor packing and determinant-coset assembly. Published algorithms and results are credited in the individual notes. [Original open question](https://arxiv.org/html/2306.03135v2)

`python -B controls.py` replays the exact finite checks of the row completion, affine block formulas and pencil example and rewrites [the check receipt](CONTROLS.json). The proofs are informal and priority is unestablished.
