# Ordinary Four-Tensor Isomorphism at Fixed Field Size

[Informal proof](PROOF.md) and [exact finite controls](check_examples.py).

For every fixed finite field, a deterministic polynomial-time algorithm for ordinary four-tensor isomorphism guarantees a decision on a fraction tending to $1-c(q)^3$ of uniformly random first inputs, against any second input. Here $c(q)=\prod_{j\geq1}(1-q^{-j})$. This gives an affirmative answer to Li–Li–Qiao–Tao–Wang Problem 1.7 in arXiv v2. On recognized inputs the same construction gives an objectwise reduction to ordinary three-tensor isomorphism of total dimension $O(n^{4/3})$.

The proof handles all positive fixed coranks, singular kernel forms and repeated primary spectra. The all-invertible sector remains outside the coverage guarantee. The theorem is informal.
