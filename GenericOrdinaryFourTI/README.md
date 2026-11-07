# High-Coverage Ordinary Four-Tensor Isomorphism

[Informal proof](PROOF.md) and [exact switch checks](check_switches.py).

For $n\geq37$, a zero-error algorithm for ordinary four-tensor isomorphism over $\mathbb F_q$ decides on at least a $1-16n^4/q$ fraction of uniformly sampled first inputs, against any second input. Its expected bit runtime is polynomial in $n$ and $\log q$, and in fixed characteristic the algorithm is deterministic. The result uses inverse-flattening covariants, a separating Laurent monomial from a weighted sum-preserving permutation, and exact multiplicative quotient computations.

For every even order $d\geq4$ the same construction gives a lower coverage bound of $1-4d\,n^{d/2+2}/q$ in polynomial dense-input time. The coverage bounds are for growing fields. The fixed-field density problem and the ordinary three-tensor problem remain open. The proof is informal.
