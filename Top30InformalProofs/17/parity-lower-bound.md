# A lower bound for parity representations

The lower bound uses the same conditional input as the [rectangular Hurwitz theorem](../02/rectangular-hurwitz.md).

## Theorem B (negative answer to Hrubeš's Problem 1, H24 §7)

A t-parity representation over F is a map φ: Even([t]) → F^D with ⟨φA,φA⟩ = 1 and ⟨φA,φB⟩ = 0 whenever A ≠ B and |A∩B| is even. Here ⟨u,v⟩ = Σu_iv_i.

**Statement.** If char F ≠ 2, every t-parity representation has

  D ≥ 2^{((√5−1)/2)·t − O(√t)} = 2^{0.618…·t − O(√t)}.

H24 asks whether D = 2^{(0.5+o(1))t} is possible over ℂ. Its claimed consequence, σ_ℂ(n,n²) ≤ n^{2+o(1)}, is false: Theorem A gives σ_F(n,n²) ≥ n^{√5−o(1)}. The previous bounds were 2^{t/2} below (H24 Remark 15) and 2^{H(1/4)t} = 2^{0.811t} above (H24 Lemma 9).

More generally, a (k,t)-parity representation (H24 (5)) has D ≥ 2^{t(√(1/4 + H(k/t)²) − 1/2) − O(√t)}. This beats H24 Remark 15 (binom(t/2, k/2)) exactly when H(k/t) > 2/3.

**Proof.**
1. **Pick n.** Take n = 16^{⌈t/8⌉}, so log₂n ∈ [t/2, t/2+4]. H24 Lemma 6 gives anticommuting, orthonormal, antisymmetric integer matrices e₁…e_t of size n×n, since ρ(n) − 1 = 2log₂n ≥ t.
2. **Restrict to sizes ≡ 0 (mod 4).** Let E = {A : |A| ≡ 0 mod 4}. Then |E| ≥ 2^{t−2} − 2^{t/2} ≥ 2^{t−3}.
   - For |A| = k ≡ 0 (mod 4), e_Aᵀ = (−1)^k(−1)^{k(k−1)/2}e_A = e_A, so e_A is symmetric.
   - H24's Theorem 11 uses one fixed k. Mixing sizes 2 and 0 (mod 4) would break the symmetric/antisymmetric match, which is why the restriction to E is needed.
3. **Build the matrices.** Set H_A = e_A ⊗ φ(A), an n × nD matrix. Then:
   - H_AH_Aᵀ = I.
   - For A ≠ B, H_AH_Bᵀ + H_BH_Aᵀ = ⟨φA,φB⟩(e_Ae_B + e_Be_A).
   - This vanishes. If |A∩B| is even, the inner product is 0. If |A∩B| is odd, e_A and e_B anticommute (H24 Lemma 8, even sets).
4. **Conclude.** By H24 Lemma 5, σ_F(n, |E|) ≤ nD. Apply Theorem A with a ≤ t/2+4 and b ≥ t−3. The function √(a²+b²) − a is decreasing in a, so
   log₂D ≥ √((t/2)² + t²) − t/2 − O(√t) = ((√5−1)/2)t − O(√t).
   The (k,t) case is the same with |E| replaced by binom(t,k). Every e_A then has the same symmetry type. ∎

**Consistency against the best upper bounds** ([local reference omitted]). I checked every point of H24 Thm 11, C(n, binom(t,k)) ≤ n·binom(t, ≤k/2), for κ = k/t ∈ (0,1):
- The upper exponent 1 + 2H(κ/2) stays above our √(1+4H(κ)²) everywhere. The margin is 0 only as κ → 0.
- The balanced point is 1.615 (H24) against √2 (ours).
- Tensor products and direct sums keep constructions above a norm, so no combination of H24 constructions contradicts Theorem A.
- **Liu's converse kill test passes:** no known composition has exponent below √(1+α²).
