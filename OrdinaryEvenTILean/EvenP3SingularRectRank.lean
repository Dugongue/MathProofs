import PolarAssemblyRank

namespace Mathproof.EvenOrdinaryTISingular.RectPolar

open scoped TensorProduct Matrix
open Module LinearMap Matrix
open Mathproof.Problem17TracePairing Mathproof.Problem17TensorEscape Mathproof.Problem17PolarAssembly

noncomputable section

variable {K : Type*} [Field K] {a b : ℕ}
abbrev RankMatrix (K : Type*) (n : ℕ) := Matrix (Fin n) (Fin n) K
abbrev RankSubspace (K : Type*) [Field K] (n : ℕ) := Submodule K (RankMatrix K n)

set_option maxHeartbeats 800000 in
theorem rank_via_tensor_sum {V : Type*} [AddCommMonoid V] [Module K V] [Module.Finite K V]
    (B : LinearMap.BilinForm K V) (P : RankMatrix K a) (Q : RankMatrix K b)
    (S : RankSubspace K a) (R : RankSubspace K b)
    (hs : ((tracePairing (K:=K)).restrict S).Nondegenerate)
    (hr : ((tracePairing (K:=K)).restrict R).Nondegenerate)
    (e : S ⊗[K] R →ₗ[K] V)
    (hB : ∀ (x x' : S) (y y' : R), B (e (x ⊗ₜ[K] y)) (e (x' ⊗ₜ[K] y')) =
      tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
        tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val) :
    finrank K (tensorSum
      ((pairingProject tracePairing S hs).comp ((matAnti P).comp S.subtype))
      ((pairingProject tracePairing R hr).comp ((matAnti Q).comp R.subtype))).range ≤
      finrank K B.range := by
  let L := (pairingProject tracePairing S hs).comp ((matAnti P).comp S.subtype)
  let N := (pairingProject tracePairing R hr).comp ((matAnti Q).comp R.subtype)
  let F : S ⊗[K] R ≃ₗ[K] Module.Dual K (S ⊗[K] R) := tensorPairing ((tracePairing (K:=K)).restrict S) ((tracePairing (K:=K)).restrict R) hs hr
  have he : B.compl₁₂ e e = F.toLinearMap.comp (tensorSum L N) := by
    apply TensorProduct.ext'
    intro x y
    apply TensorProduct.ext'
    intro x' y'
    change B (e (x ⊗ₜ[K] y)) (e (x' ⊗ₜ[K] y')) =
      F (tensorSum L N (x ⊗ₜ[K] y)) (x' ⊗ₜ[K] y')
    rw [hB]
    simp only [tensorSum, LinearMap.add_apply, TensorProduct.map_tmul, LinearMap.id_apply,
      map_add, F, tensorPairing_tmul]
    change _ =
      (tracePairing (L x).val x'.val) * tracePairing y.val y'.val +
        tracePairing x.val x'.val * tracePairing (N y).val y'.val
    simp only [L, N, LinearMap.comp_apply, Submodule.subtype_apply, pairingProject_pair]
  have hb := rank_pullback_le B e
  rw [he, rank_comp_pairing F] at hb
  exact hb


theorem finrank_of_codim_le {n : ℕ} {X : RankSubspace K n} {k : ℕ}
    (h : finrank K (RankMatrix K n ⧸ X) ≤ k) :
    n * n - k ≤ finrank K X := by
  have hx := X.finrank_quotient_add_finrank
  simp only [finrank_matrix, Fintype.card_fin, Module.finrank_self, mul_one] at hx
  omega

theorem nondegenerate_restriction {n : ℕ} {X : RankSubspace K n} {c : ℕ}
    (h : finrank K (RankMatrix K n ⧸ X) ≤ c) :
    ∃ U : RankSubspace K n, U ≤ X ∧
      ((tracePairing (K := K) (ι := Fin n)).restrict U).Nondegenerate ∧
      finrank K (RankMatrix K n ⧸ U) ≤ 2*c := by
  obtain ⟨U, hUX, hn, hc⟩ := exists_nondegenerate_subspace
    tracePairing tracePairing_symmetric tracePairing_nondegenerate X
  exact ⟨U, hUX, hn, hc.trans (Nat.mul_le_mul_left 2 h)⟩


variable {S : RankSubspace K a} {R : RankSubspace K b}

/-- Formula for the restricted polar form on elementary tensors. -/
def HasPolarFormula (B : LinearMap.BilinForm K (S ⊗[K] R)) (P : RankMatrix K a) (Q : RankMatrix K b) : Prop :=
  ∀ (x x' : S) (y y' : R), B (x ⊗ₜ[K] y) (x' ⊗ₜ[K] y') =
    tracePairing (matAnti P x.val) x'.val * tracePairing y.val y'.val +
    tracePairing x.val x'.val * tracePairing (matAnti Q y.val) y'.val

/- Restricted polar rank of the anticommutator tensor sum in the nonscalar case. -/
set_option maxHeartbeats 900000 in
theorem polar_rank_of_nonscalar_left (P : RankMatrix K a) (Q : RankMatrix K b)
    (B : LinearMap.BilinForm K (S ⊗[K] R)) (hB : HasPolarFormula B P Q)
    (hP : ∀ z : K, P ≠ z • (1 : RankMatrix K a)) (c : ℕ)
    (hSc : finrank K (RankMatrix K a ⧸ S) ≤ c) (hRc : finrank K (RankMatrix K b ⧸ R) ≤ c) :
    (a - 4*c) * (b*b - 2*c) ≤ finrank K B.range := by
  obtain ⟨U, hUS, hU, hUc⟩ := nondegenerate_restriction hSc
  obtain ⟨W, hWR, hW, hWc⟩ := nondegenerate_restriction hRc
  let e : U ⊗[K] W →ₗ[K] S ⊗[K] R :=
    TensorProduct.map (Submodule.inclusion hUS) (Submodule.inclusion hWR)
  have he := rank_via_tensor_sum B P Q U W hU hW e (by
    intro x x' y y'
    simp only [e, TensorProduct.map_tmul]
    simpa only [Submodule.coe_inclusion] using hB
      (Submodule.inclusion hUS x) (Submodule.inclusion hUS x')
      (Submodule.inclusion hWR y) (Submodule.inclusion hWR y'))
  let tr : LinearMap.BilinForm K (RankMatrix K a) := tracePairing
  let tr' : LinearMap.BilinForm K (RankMatrix K b) := tracePairing
  let π : RankMatrix K a →ₗ[K] U := pairingProject tr U hU
  let N : End K W := (pairingProject tr' W hW).comp ((matAnti Q).comp W.subtype)
  have hrank := rank_compressed_matAnti P hP U W N π (pairingProject_split tr U hU)
  simp only [Fintype.card_fin] at hrank
  have hFirst : a - 4*c ≤ a - 2 * finrank K (RankMatrix K a ⧸ U) := by omega
  exact (Nat.mul_le_mul hFirst (finrank_of_codim_le hWc)).trans (hrank.trans he)

/- Swapping the roles of the two factor spaces yields the same lower bound. -/
set_option maxHeartbeats 900000 in
theorem polar_rank_of_nonscalar_right (P : RankMatrix K a) (Q : RankMatrix K b)
    (B : LinearMap.BilinForm K (S ⊗[K] R)) (hB : HasPolarFormula B P Q)
    (hQ : ∀ z : K, Q ≠ z • (1 : RankMatrix K b)) (c : ℕ)
    (hSc : finrank K (RankMatrix K a ⧸ S) ≤ c) (hRc : finrank K (RankMatrix K b ⧸ R) ≤ c) :
    (b - 4*c) * (a*a - 2*c) ≤ finrank K B.range := by
  let cT := TensorProduct.comm K R S
  let B' := B.compl₁₂ cT.toLinearMap cT.toLinearMap
  have hB' : HasPolarFormula B' Q P := by
    intro x x' y y'
    change B (cT (x ⊗ₜ[K] y)) (cT (x' ⊗ₜ[K] y')) = _
    simp only [cT, TensorProduct.comm_tmul]
    rw [hB]
    ac_rfl
  have hr := polar_rank_of_nonscalar_left Q P B' hB' hQ c hRc hSc
  rwa [rank_pullback_equiv] at hr

end
end Mathproof.EvenOrdinaryTISingular.RectPolar

#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.polar_rank_of_nonscalar_left
#print axioms Mathproof.EvenOrdinaryTISingular.RectPolar.polar_rank_of_nonscalar_right


