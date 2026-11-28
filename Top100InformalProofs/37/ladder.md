# Implementing tensor stabilizer constraints with ladders

The size bound is polynomial in the displayed marker space and tensor input size.

## The ladder lemma

Let F be any field. Take a multi-sorted system:
- vector spaces V₁, …, V_q;
- tensors t_j, each in a tensor product of k_j ≤ d factors from the V_i and V_i*.

The group ∏ GL(V_i) acts. For each t_j with k = k_j > 3 and legs L₁, …, L_k, add auxiliary sorts X₂, …, X_{k−1} with X_r := L₁ ⊗ ⋯ ⊗ L_r, together with:
- **markers** μ_r ∈ X_{r−1}* ⊗ L_r* ⊗ X_r for 2 ≤ r ≤ k−1 (with X₁ := L₁), each the canonical isomorphism X_{r−1} ⊗ L_r → X_r. These have arity 3;
- t_j itself, now viewed in X_{k−1} ⊗ L_k (arity 2).

**Claim:** isomorphisms of the new system restrict bijectively to isomorphisms of the old one.
- Each μ_r is bijective, so preserving it forces h_{X_r} = h_{X_{r−1}} ⊗ g_{L_r}.
- Inductively, h_{X_r} = g_{L₁} ⊗ ⋯ ⊗ g_{L_r}.
- Then preserving t_j is the original condition. Conversely, every old isomorphism extends. ∎

The auxiliary dimensions are at most the size of t_j itself, so the new system has size linear in the input, and the graph has O(Σ k_j) vertices.

## Theorem 10.4 (answer to GQ OQ 10.4)

**For every fixed d ≥ 3, isomorphism of any fixed-shape system of tensors of order ≤ d over any field reduces, by a uniform p-projection of polynomial size, to d-Tensor Isomorphism.**

*Proof.*
1. Apply the ladder lemma to get an arity-≤3 system.
2. FGS Theorem 1.1 (any field) turns it into 3TI. Its size is polynomial in the dimensions times 2^{O(#parts)}, a constant for a fixed shape.
3. 3TI ≤ dTI by appending d−3 one-dimensional modes; the scalars absorb.
4. Every step is a p-projection with 0/1 constants. ∎

So the GI analogy of GQ §10 is complete: **dTI is universal for basis-explicit linear structures of arity ≤ d, for every d.**

## Two published theorems get short proofs

1. **GQ Theorem B (dTI ≤ 3TI), qualitatively.** Apply the ladder to a single d-tensor, then FGS. GQ's path-algebra proof gives the explicit dimension O(d² n^{d−1}). The ladder proof gives an unspecified polynomial. So it is simpler but weaker in size, and the Lean `BalancedOrdinaryReduction` (O(n^⌈d/3⌉)) remains the size-optimal route. What the ladder adds is that it works verbatim in settings where path algebras break, as below.
2. **CGQTZ Theorem 1.13 (d-TI_G ≤ 3-TI_G for G = U over ℂ, O over ℝ).** CGQTZ call a new path-algebra construction their "main technical contribution" here, because Mal'cev conjugacy of Wedderburn complements fails for unitary conjugation.
   - **Ladder proof:** give each X_r the tensor-product Hermitian (or Euclidean) form. The forced h_{X_r} = u₁ ⊗ ⋯ ⊗ u_r is then automatically unitary.
   - The system has c = d−1 tensors. CGQTZ's own Theorem 5.1 (the unitary FGS, size poly(Σ dims, 2^{poly(c)})) finishes. ∎

## New: the symplectic version, every field

**Corollary Sp.** For every field and fixed d, **d-TI_Sp ≤ 3-TI_Sp**, and likewise for the five actions. This case is not covered by CGQTZ, who list symplectic groups as the stumbling block.

*Proof.*
1. d-TI_Sp reduces to an arity-≤d GL-system: the tensor plus the symplectic forms ω_i on each V_i (arity 2).
2. The ladder plus FGS give 3TI over GL.
3. 3TI ≤ 3-TI_Sp by Theorem S, since Sp_{2m} has the Siegel Levi GL_m (Lean `LeviHardness.lean`, together with `ti_eq_tisp`). ∎

The same route gives d-TI_G ≤ 3-TI_G for every form group G with a GL_m-Levi section, m ≥ n^ε. This covers:
- O with large Witt index, over any field of characteristic ≠ 2;
- U over finite fields, together with UNITARY-FINITE-FIELDS.md;
- O(p,q) with min(p,q) ≥ n^ε.
