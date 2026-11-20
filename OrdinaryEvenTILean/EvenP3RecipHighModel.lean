import EvenP3RecipHighBatchRepeat
import EvenP3RecipHighRowProbability
import EvenP3RecipHighUnion

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)

noncomputable section

variable {K I B A L C Λ : Type*} [Field K] [Fintype K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C] [Fintype Λ]
variable [DecidableEq I] [DecidableEq B] [DecidableEq A] [DecidableEq C] [DecidableEq L]

/-- Under the literal independent column and row sampling model, the probability
that any high label's cross map has a nonzero column kernel is bounded by
its exposed-column span budget plus the row testing budget. -/
theorem high_model_bad_mass_le (s g d h ρ : ℕ)
    (T : Λ → Matrix I I K →ₗ[K] Matrix I I K) (U : L → Matrix I B K)
    (W : Submodule K (Matrix B I K))
    (hU : ∀ w : L → K, w ≠ 0 → Fintype.card I - d ≤ (primalCombination U w).rank)
    (hρ : ∀ z, ρ + finrank K (Matrix B I K ⧸ W) + 2 * (Fintype.card I * d) ≤
      finrank K (T z).range)
    (hh : h + finrank K (Matrix B I K ⧸ W) ≤ Fintype.card A * Fintype.card L) :
    uniformFraction ((((Fin s × A) → C → W) × (Fin g → (Fin s × A) → W)))
      (fun p => ∃ z : Λ, ∃ y : C → (Fin s × A) → L → K, y ≠ 0 ∧
        ∀ t, rowEvaluation (T z) U p.1 y (p.2 t) = 0) ≤
      (Fintype.card (Λ × (C → L → K)) : ℝ) *
        ((Fintype.card K : ℝ)^(Fintype.card A * Fintype.card L) / (Fintype.card K : ℝ)^ρ)^s +
      (Fintype.card Λ : ℝ) * ((Nat.card (C → (Fin s × A) → L → K) : ℝ) /
        (Fintype.card K : ℝ)^(g*h)) := by
  letI : Fintype W := Fintype.ofFinite _
  let Col := (Fin s × A) → C → W
  let Row := Fin g → (Fin s × A) → W
  let Z := C → L → K
  let P (z : Λ × Z) (c : Col) := z.2 ≠ 0 ∧
    finrank K (Submodule.span K (Set.range (batchVector (T z.1) U
      (fun t => primalCombination U (z.2 t)) c))) < Fintype.card A * Fintype.card L
  let Bad (c : Col) := ∃ z : Λ × Z, P z c
  let Fail (c : Col) (r : Row) := ∃ z : Λ, ∃ y : C → (Fin s × A) → L → K, y ≠ 0 ∧
    ∀ t, rowEvaluation (T z) U c y (r t) = 0
  let η := ((Fintype.card K : ℝ)^(Fintype.card A * Fintype.card L) / (Fintype.card K : ℝ)^ρ)^s
  let θ := (Fintype.card Λ : ℝ) * ((Nat.card (C → (Fin s × A) → L → K) : ℝ) /
    (Fintype.card K : ℝ)^(g*h))
  have hcol (z : Λ × Z) : uniformFraction Col (P z) ≤ η := by
    by_cases hz : z.2 = 0
    · have he : P z = fun _ => False := by funext c; simp [P,hz]
      rw [he]
      simp [uniformFraction] <;> positivity
    · have hm : ∃ t, Fintype.card I - d ≤ (primalCombination U (z.2 t)).rank := by
        obtain ⟨t,ht⟩ : ∃ t, z.2 t ≠ 0 := by
          by_contra hn
          apply hz
          funext t
          by_contra ht
          exact hn ⟨t,ht⟩
        exact ⟨t,hU _ ht⟩
      exact (uniformFraction_le_of_imp (fun _ hx => hx.2)).trans
        (bad_full_column_span_le s (T z.1) U _ W d ρ hU hm (hρ z.1))
  have hbad : uniformFraction Col Bad ≤ (Fintype.card (Λ × Z) : ℝ) * η :=
    uniformFraction_union_const P η hcol
  have hrow (c : Col) (hc : ¬ Bad c) : uniformFraction Row (Fail c) ≤ θ := by
    apply uniformFraction_union_const
    intro z
    apply row_failure_fraction_of_column_span (T z) U c g h
    intro w hw
    apply hh.trans
    by_contra! hsmall
    exact hc ⟨(z,w),hw,hsmall⟩
  have hmodel := exposed_rows_bound Bad Fail θ (by positivity) hrow
  exact hmodel.trans (add_le_add hbad le_rfl)

#print axioms high_model_bad_mass_le

end
end Mathproof.EvenTI.Reciprocal.Four