import EvenP4Coverage
import EvenSolverAssembly

namespace Mathproof.EvenTI.GlobalCoverage

open scoped Classical
open EvenTI.Action EvenTI.Primary EvenTI.Contract

noncomputable section

variable {K : Type} [Field K] [Fintype K]

/-- The mathematical predicate with the Boolean interface used by the
verified word adapter. The executable test is part of the trial driver. -/
def coverageAccept (K : Type) [Field K] [Fintype K] :
    ∀ {d n : ℕ}, Tensor K d n → Bool := fun T => sourceAccept T

theorem rejectedSourceFraction_eq_event (d n : ℕ) :
    rejectedSourceFraction (coverageAccept K) d n =
      event (fun T : Tensor K d n => ¬ sourceAccepted T) := by
  have h (T : Tensor K d n) : coverageAccept K T = false ↔ ¬ sourceAccepted T := by
    rw [← sourceAccept_eq_true T]
    change sourceAccept T = false ↔ ¬ sourceAccept T = true
    cases sourceAccept T <;> simp
  rw [event_eq_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  unfold rejectedSourceFraction
  congr 2
  apply congrArg Finset.card
  exact Finset.filter_congr fun T _ => h T

/-- The exact uniform coverage premise of `assembleVerifiedSolver`. -/
theorem contract_uniformCoverage (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ d n : ℕ, 4 ≤ d → Even d → N ≤ n →
      rejectedSourceFraction (coverageAccept K) d n ≤ ε := by
  obtain ⟨N, hN, h⟩ := uniformCoverage K ε hε
  refine ⟨N, hN, fun d n hd he hn => ?_⟩
  rw [rejectedSourceFraction_eq_event]
  exact h d n hd he hn

/-- The exact higher-order-rate premise of `assembleVerifiedSolver`. -/
theorem contract_higherOrderRate :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 2 ≤ N ∧ ∀ d n : ℕ, 6 ≤ d → Even d → N ≤ n →
      rejectedSourceFraction (coverageAccept K) d n ≤ C / Real.log n := by
  obtain ⟨C, hC, N, hN, h⟩ := higherOrderRate K
  refine ⟨C, hC, N, hN, fun d n hd he hn => ?_⟩
  rw [rejectedSourceFraction_eq_event]
  exact h d n hd he hn

theorem decoded_word_rejection_eq [DecidableEq K] (F : FieldEncoding K) {d n : ℕ}
    (hd : 4 ≤ d) (he : Even d) (hn : 2 ≤ n) :
    rejectDensity F (recognizeWords F (coverageAccept K)) d n =
      event (fun T : Tensor K d n => ¬ sourceAccepted T) :=
  (rejectedSourceFraction_eq F (coverageAccept K) hd he hn).trans
    (rejectedSourceFraction_eq_event d n)

#print axioms contract_uniformCoverage
#print axioms contract_higherOrderRate
#print axioms decoded_word_rejection_eq

end
end Mathproof.EvenTI.GlobalCoverage
