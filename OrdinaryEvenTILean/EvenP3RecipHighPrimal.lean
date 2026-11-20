import EvenP2Corank

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap EvenTI.Primary
open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Singular.Coverage
open Mathproof.EvenTI.Singular.Forms (mulVec_zero_fraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp uniformFraction_exists_le)

noncomputable section

variable {K I B L : Type*} [Field K] [Fintype K]
variable [Fintype I] [Fintype B] [Fintype L] [DecidableEq I] [DecidableEq B] [DecidableEq L]

theorem rectangular_rank_tail (hshape : Fintype.card I ≤ Fintype.card B) (d : ℕ) :
    uniformFraction (Matrix I B K) (fun U => U.rank < Fintype.card I - d) ≤
      2 / (Fintype.card K : ℝ)^d := by
  let e := (Matrix.transposeLinearEquiv I B K K).toEquiv
  let A (U : Matrix I B K) : (I → K) →ₗ[K] (B → K) := Matrix.toLin' Uᵀ
  have hq₀ : (0 : ℕ) < Fintype.card K := Fintype.card_pos
  have hq : (1 : ℕ) < Fintype.card K := Fintype.one_lt_card
  have h0 (v : I → K) (hv : v ≠ 0) :
      event (fun U : Matrix I B K => A U v = 0) ≤ (Fintype.card (I → K) : ℝ)⁻¹ := by
    rw [event_as_fraction]
    change uniformFraction (Matrix I B K) (fun U => Uᵀ.mulVec v = 0) ≤ _
    rw [show (fun U : Matrix I B K => Uᵀ.mulVec v = 0) =
       (fun U => (e U).mulVec v = 0) from rfl,
      uniformFraction_equiv e (fun A => A.mulVec v = 0), mulVec_zero_fraction v hv, Fintype.card_fun, Nat.cast_pow, ← one_div]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by exact_mod_cast hq.le) hshape)
  have m := large_kernel_fraction A (Fintype.card K ^ d) (pow_pos hq₀ _) h0
  rw [event_as_fraction, Nat.cast_pow] at m
  refine (uniformFraction_le_of_imp ?_).trans m
  intro U hU
  apply pow_lt_pow_right₀ hq
  have h := (A U).finrank_range_add_finrank_ker
  have hr : finrank K (A U).range = U.rank := by
    change finrank K (Matrix.toLin' Uᵀ).range = U.rank
    rw [Matrix.toLin'_apply', ← Matrix.rank, Matrix.rank_transpose]
  rw [hr, Module.finrank_pi] at h
  omega

private def comboLin (w : L → K) : (L → Matrix I B K) →ₗ[K] Matrix I B K where
  toFun U := ∑ b, w b • U b
  map_add' U V := by simp [Pi.add_apply, smul_add, Finset.sum_add_distrib]
  map_smul' a U := by simp [Pi.smul_apply, smul_comm (w _) a, Finset.smul_sum]

private theorem comboLin_surjective (w : L → K) (hw : w ≠ 0) :
    Function.Surjective (comboLin (K := K) (I := I) (B := B) w) := by
  obtain ⟨b,hb⟩ : ∃ b, w b ≠ 0 := by
    by_contra h
    apply hw
    funext b
    by_contra hb
    exact h ⟨b,hb⟩
  intro U
  refine ⟨Pi.single b ((w b)⁻¹ • U), ?_⟩
  change (∑ j, w j • Pi.single b ((w b)⁻¹ • U) j) = U
  rw [Finset.sum_eq_single b]
  · simp [smul_smul, hb]
  · intro j _ h
    simp [Pi.single_eq_of_ne h]
  · simp

/-- A uniformly sampled primal pool has high row rank for every nonzero
linear combination except on this explicit small exceptional fraction. -/
theorem primal_pool_rank_tail (hshape : Fintype.card I ≤ Fintype.card B) (d : ℕ) :
    uniformFraction (L → Matrix I B K) (fun U => ∃ w : L → K, w ≠ 0 ∧
      (∑ b, w b • U b : Matrix I B K).rank < Fintype.card I - d) ≤
      (Fintype.card K : ℝ)^Fintype.card L * (2 / (Fintype.card K : ℝ)^d) := by
  let Q (V : Matrix I B K) := V.rank < Fintype.card I - d
  let W := {w : L → K // w ≠ 0}
  letI : Fintype W := Fintype.ofFinite _
  let P (w : W) (U : L → Matrix I B K) := Q (comboLin w.val U)
  have h : ∀ U, (∃ w : L → K, w ≠ 0 ∧ Q (∑ b, w b • U b)) → ∃ w : W, P w U := by
    rintro U ⟨w,hw,hU⟩
    exact ⟨⟨w,hw⟩,hU⟩
  have hU := (uniformFraction_le_of_imp h).trans (uniformFraction_exists_le P)
  refine hU.trans ?_
  have hcard : (Fintype.card W : ℝ) ≤ (Fintype.card K : ℝ)^Fintype.card L := by
    rw [← Nat.cast_pow, ← Fintype.card_fun]
    exact_mod_cast (Fintype.card_le_of_injective Subtype.val Subtype.val_injective)
  calc
    _ ≤ ∑ _ : W, 2 / (Fintype.card K : ℝ)^d := by
      apply Finset.sum_le_sum
      intro w _
      unfold P
      rw [uniformFraction_linear_surjective (comboLin w.val) (comboLin_surjective w.val w.property)]
      exact rectangular_rank_tail hshape d
    _ = (Fintype.card W : ℝ) * (2 / (Fintype.card K : ℝ)^d) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

#print axioms rectangular_rank_tail
#print axioms primal_pool_rank_tail

end
end Mathproof.EvenTI.Reciprocal.Four