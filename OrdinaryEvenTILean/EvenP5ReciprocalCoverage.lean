import EvenP5TrialList
import EvenP5InvTransport

namespace EvenTI.TrialProducer

open scoped BigOperators
open Matrix EvenTI.Action EvenTI.Contract
open Mathproof.EvenTI.Reciprocal.Coverage Mathproof.EvenTI.OrderFour
open Mathproof.Problem17RepeatedBudget

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {l n : ℕ}

noncomputable def reciprocalBudget (A : HigherModes l → Matrix (Fin n) (Fin n) K) : ℕ :=
  ∑ i, repeatedBudget (A i).charpoly

theorem reciprocalBudget_follow (g : Changes K ((l + 1) + (l + 1)) n)
    (A : HigherModes l → Matrix (Fin n) (Fin n) K) :
    reciprocalBudget (conjugateReciprocalAnchors g A) = reciprocalBudget A := by
  unfold reciprocalBudget
  apply Finset.sum_congr rfl
  intro i _
  rw [conjugateReciprocalAnchors, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc,
    Units.inv_val, Matrix.one_mul]

/-- On the invertible cut, both actual lists contain exactly their reciprocal
trial. Every physical mode of that trial is carried by the same transporter. -/
theorem reciprocalTrials_follow (F : FieldEncoding K) (T : Dense K l n)
    (g : Changes K ((l + 1) + (l + 1)) n) (hn : 1 ≤ n)
    (h : IsUnit (flatten (l := l + 1) (r := l + 1) T)) :
    ∃ A : HigherModes l → Matrix (Fin n) (Fin n) K,
      prepareTrials F T = [.reciprocal A] ∧
      prepareTrials F (act g T) = [.reciprocal (conjugateReciprocalAnchors g A)] ∧
      reciprocalBudget A = higherReciprocalBudget hn ⟨T, h⟩ := by
  let A := fun i => higherDenseModeAnchor hn i (⟨T,h⟩ : InvertibleCut K (l + 1) n)
  have hA : rawReciprocalAnchors T = some A := rawReciprocalAnchors_eq_higher hn ⟨T,h⟩
  have hgA := rawReciprocalAnchors_target hn g rfl hA
  exact ⟨A, prepareTrials_reciprocal F T _ hA, prepareTrials_reciprocal F (act g T) _ hgA, rfl⟩

set_option maxHeartbeats 800000 in
/-- The specialized order-four source budget is the budget of the matrices
that actually appear in the reciprocal trial. -/
theorem fourReciprocalTrials_follow (F : FieldEncoding K) (T : Dense K 1 n)
    (g : Changes K (2 + 2) n) (hn : 5 ≤ n) (h : IsUnit (flatten (l := 2) (r := 2) T)) :
    ∃ A : HigherModes 1 → Matrix (Fin n) (Fin n) K,
      prepareTrials F T = [.reciprocal A] ∧
      prepareTrials F (act g T) = [.reciprocal (conjugateReciprocalAnchors g A)] ∧
      reciprocalBudget A = squareReciprocalBudget hn ⟨T, h⟩ := by
  let A := fun i => squareDenseModeAnchor hn i (⟨T,h⟩ : InvertibleCut K 2 n)
  have hA : rawReciprocalAnchors (l := 1) T = some A := rawReciprocalAnchors_eq_square hn ⟨T,h⟩
  have hgA := rawReciprocalAnchors_target (l := 1) (by omega) g rfl hA
  exact ⟨A, prepareTrials_reciprocal F T _ hA, prepareTrials_reciprocal F (act g T) _ hgA, rfl⟩

#print axioms reciprocalBudget_follow
#print axioms reciprocalTrials_follow
#print axioms fourReciprocalTrials_follow

end EvenTI.TrialProducer
