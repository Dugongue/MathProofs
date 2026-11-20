import EvenP3RecipHighRow

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Module LinearMap
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (zero_tuple_fraction uniformFraction_le_of_imp
  uniformFraction_exists_le)

noncomputable section

variable {K I B A L C : Type*} [Field K] [Fintype K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C]
variable [DecidableEq I] [DecidableEq B] [DecidableEq A] [DecidableEq L]

/-- With the column pool fixed, each nonzero candidate must pass independent
linear tests from all live row groups. -/
theorem row_failure_fraction (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) {W : Submodule K (Matrix B I K)} (cols : A → C → W)
    (r d : ℕ) (hRank : ∀ y : C → A → L → K, y ≠ 0 →
      d ≤ finrank K (rowEvaluation T U cols y).range) :
    uniformFraction (Fin r → A → W) (fun rows => ∃ y : C → A → L → K, y ≠ 0 ∧
      ∀ t, rowEvaluation T U cols y (rows t) = 0) ≤
      (Nat.card (C → A → L → K) : ℝ) / (Fintype.card K : ℝ)^(r*d) := by
  letI : Fintype W := Fintype.ofFinite _
  let Y := {y : C → A → L → K // y ≠ 0}
  letI : Fintype Y := Fintype.ofFinite _
  let P (y : Y) (rows : Fin r → A → W) := ∀ t, rowEvaluation T U cols y.val (rows t) = 0
  have hs : ∀ rows, (∃ y : C → A → L → K, y ≠ 0 ∧
      ∀ t, rowEvaluation T U cols y (rows t) = 0) → ∃ y : Y, P y rows := by
    rintro rows ⟨y,hy,h⟩
    exact ⟨⟨y,hy⟩,h⟩
  have hsum := (uniformFraction_le_of_imp hs).trans (uniformFraction_exists_le P)
  have hq : (1 : ℝ) ≤ Fintype.card K := by exact_mod_cast (Fintype.one_lt_card (α := K)).le
  have hq' : (0 : ℝ) < Fintype.card K := by linarith
  have hcard : Fintype.card Y ≤ Fintype.card (C → A → L → K) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  refine hsum.trans ?_
  calc
    _ ≤ ∑ _ : Y, 1 / (Fintype.card K : ℝ)^(r*d) := by
      apply Finset.sum_le_sum
      intro y _
      unfold P
      rw [zero_tuple_fraction]
      apply one_div_le_one_div_of_le (pow_pos hq' _)
      exact pow_le_pow_right₀ hq (Nat.mul_le_mul_left r (hRank y.val y.property))
    _ = (Fintype.card Y : ℝ) / (Fintype.card K : ℝ)^(r*d) := by simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      rw [Nat.card_eq_fintype_card]
      exact_mod_cast hcard

/-- A lower bound on each nonzero tuple's column coefficient span suffices
for the entire row-group kernel test. -/
theorem row_failure_fraction_of_column_span (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) {W : Submodule K (Matrix B I K)} (cols : A → C → W)
    (r d : ℕ) (hSpan : ∀ z : C → L → K, z ≠ 0 →
      d + finrank K (Matrix B I K ⧸ W) ≤ finrank K (Submodule.span K (Set.range
        (batchVector T U (fun t => primalCombination U (z t)) cols)))) :
    uniformFraction (Fin r → A → W) (fun rows => ∃ y : C → A → L → K, y ≠ 0 ∧
      ∀ t, rowEvaluation T U cols y (rows t) = 0) ≤
      (Nat.card (C → A → L → K) : ℝ) / (Fintype.card K : ℝ)^(r*d) := by
  apply row_failure_fraction T U cols r d
  intro y hy
  obtain ⟨a,ha⟩ : ∃ a : A, (fun t => y t a) ≠ 0 := by
    by_contra h
    apply hy
    funext t a j
    have ha : (fun t => y t a) = 0 := by
      by_contra ha
      exact h ⟨a,ha⟩
    exact congrFun (congrFun ha t) j
  have h := (hSpan _ ha).trans (rowEvaluation_rank T U cols y a)
  omega

#print axioms row_failure_fraction
#print axioms row_failure_fraction_of_column_span

end
end Mathproof.EvenTI.Reciprocal.Four