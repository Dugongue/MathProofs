import EvenP12CountPostNormalize

namespace EvenTI.P12CountPost

open EvenTI.Action EvenTI.Contract EvenTI.Counting EvenTI.P10Oracle
open Lax51.TuringPolytime
set_option autoImplicit false

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {q : ℕ}

/-- Post only observes the comparison success tag. Witness choices in the
comparison output have no effect on the count, including on malformed input. -/
theorem postNormalize_congr_success (enum : Fin q ≃ Kˣ) (w a b : List ℕ)
    (h : a.head? = some 2 ↔ b.head? = some 2) :
    postNormalize enum w a = postNormalize enum w b := by
  unfold postNormalize postNormalizeParsed
  cases postZSource w <;> simp [h]

theorem countPostZ_turingPolytime_of_normalize_success (F : FieldEncoding K) (P : TrialPlan K)
    (enum : Fin q ≃ Kˣ) (compare : List ℕ → List ℕ)
    (hSuccess : ∀ x, (compareWords F P x).head? = some 2 ↔ (compare x).head? = some 2)
    (h : TuringPolytime (fun w => postNormalize enum w (compare (postZSource w)))) :
    TuringPolytime (countPostZ F P enum) := by
  apply countPostZ_turingPolytime_of_normalize
  rw [show (fun w => postNormalize enum w (compareWords F P (postZSource w))) =
      (fun w => postNormalize enum w (compare (postZSource w))) from
    funext (fun w => postNormalize_congr_success enum w _ _ (hSuccess _))]
  exact h

#print axioms postNormalize_congr_success
#print axioms countPostZ_turingPolytime_of_normalize_success
end EvenTI.P12CountPost
