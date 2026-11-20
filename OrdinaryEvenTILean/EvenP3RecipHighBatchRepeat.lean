import EvenP3RecipHighBatch
import EvenP3RecipHighRepeat

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenOrdinaryTISingular

noncomputable section

variable {K I B A L C : Type*} [Field K] [Fintype K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C]
variable [DecidableEq I] [DecidableEq B] [DecidableEq A] [DecidableEq C]

/-- At least one independent batch gives a certificate of the required
coefficient span, with the true product-law bound before conditioning. -/
theorem bad_full_column_span_le (s : ℕ)
    (T : Matrix I I K →ₗ[K] Matrix I I K) (U : L → Matrix I B K)
    (M : C → Matrix I B K) (W : Submodule K (Matrix B I K)) (d r : ℕ)
    (hU : ∀ w : L → K, w ≠ 0 → Fintype.card I - d ≤ (primalCombination U w).rank)
    (hM : ∃ t, Fintype.card I - d ≤ (M t).rank)
    (hr : r + finrank K (Matrix B I K ⧸ W) + 2 * (Fintype.card I * d) ≤ finrank K T.range) :
    uniformFraction ((Fin s × A) → C → W) (fun V =>
      finrank K (Submodule.span K (Set.range (batchVector T U M V))) <
        Fintype.card A * Fintype.card L) ≤
      ((Fintype.card K : ℝ)^(Fintype.card A * Fintype.card L) / (Fintype.card K : ℝ)^r)^s := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  let e := (Equiv.curry (Fin s) A (C → W)).symm
  have h0 := bad_column_batch_le (A := A) T U M W d r hU hM hr
  have hb := deficient_span_repeated_bound (fun V : A → C → W => batchVector T U M V) s _ h0
  rw [Fintype.card_prod] at hb
  rw [← uniformFraction_equiv e]
  refine le_trans ?_ hb
  apply Mathproof.EvenTI.Reciprocal.PartOne.uniformFraction_le_of_imp
  intro x hx
  have he : Set.range (batchVector T U M (e x)) =
      Set.range (fun j : Fin s × (A × L) => batchVector T U M (x j.1) j.2) := by
    ext z
    constructor
    · rintro ⟨⟨⟨i,a⟩,b⟩,rfl⟩
      exact ⟨(i,(a,b)),rfl⟩
    · rintro ⟨⟨i,⟨a,b⟩⟩,rfl⟩
      exact ⟨((i,a),b),rfl⟩
  rw [← he]
  exact hx

#print axioms bad_full_column_span_le

end
end Mathproof.EvenTI.Reciprocal.Four