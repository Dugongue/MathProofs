# Fractional-Exponent Tensor Order Reduction

[Informal proofs](PROOFS.md) and an [exact finite-field example checker](check_examples.py).

This note extends the balanced reduction toward Grochow–Qiao Question 7.8. Intrinsic flattening supports and centroid blocks give size bounds in terms of the input structure. Over fixed finite fields, spectral canonization attains $O(n^{d/3})$ on a checkable promise, including full-pair-rank order-four examples. The fixed-lift lower bound proves that a single group homomorphism with orbitwise injectivity forces maximum width at least $n^{\lceil d/3\rceil}$. The unrestricted polynomial-time reduction remains open.

Run the example checks with Python 3. They verify the covariant hypotheses in the examples. The new theorems are informal.
