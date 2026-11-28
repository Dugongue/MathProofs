# A degree lower bound from finite-field Galois forms

The proof distinguishes proof systems with and without the finite-field equations.

## The witness

**Construction.** Let F = F_q, choose u ∈ F_{q²}² \ F_q², and let ū be its Frobenius conjugate. Set

  T₁ = e₁⊗e₁⊗e₁ + e₂⊗e₂⊗e₂,  T₂ = u⊗u⊗u + ū⊗ū⊗ū.

**Properties.**
1. **T₂ is F_q-rational.** It is Frobenius-invariant.
2. **They are isomorphic over F_{q²}.** Take P = [u ū], invertible, in all three modes.
3. **They are not isomorphic over F_q.** T₁ has F_q-rank 2. T₂ has F_q-rank 3: its unique rank-2 decomposition over F̄ (Kruskal) consists of Galois-conjugate rank-one terms, so no rational rank-2 decomposition exists. Brute force over GL₂(F_q)³ finds **0 isomorphisms** for q = 2, 3, 5.
4. **Padding.** Pad by zeros to n×n×n for any n ≥ 2.
5. **Rank.** Both tensors have rank ≤ 3 over F_q, and rank 2 over F̄.

## Theorem G1

For every finite field F_q and every n ≥ 2, there are n×n×n tensors of rank ≤ 3 that are non-isomorphic over F_q and satisfy the following.

1. **(No equational refutation.)** Without the axioms x^q − x, the isomorphism equations over F_q (XA = …, XX⁻¹ = I) have **no Nullstellensatz or PC refutation of any degree**. They have solutions over F̄_q (property 2), and an NS or PC refutation over F_q is also one over F̄_q.
2. **(Field axioms cost degree q.)** With the axioms x^q − x, every NS or PC refutation has **degree ≥ q**. A refutation must use some field axiom, since otherwise it would refute the F̄-satisfiable system, and every field axiom has degree q.

The same works over ℝ and ℚ with real or rational forms (as in Grochow–Qiao Example 10.7). There, purely equational systems again cannot refute, and Positivstellensatz/SoS-type inequalities are required.
