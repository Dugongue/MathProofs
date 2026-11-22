import EvenP18ReciprocalTrial
import EvenP16AnchorWordClock

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace EvenTI.P18Execution

open EvenTI.Action EvenTI.Contract EvenTI.P12ComparePrep EvenTI.P12Compare
open EvenTI.P15Execution EvenTI.P16Execution EvenTI.P17Execution
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Lax51.BinaryWordEncoding Polynomial

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

/-- The inverse, units, record header and two full anchor sweeps take a
polynomial number of operations in the original pair's binary size. -/
theorem produceReciprocalTrial_originalBits (D : FieldEncoding K) (F : FieldPresentation K) :
    ∃ p : Polynomial ℕ, ∀ {l n : ℕ} (T U : Tensor K ((l+1)+(l+1)) n), 2 ≤ n →
      produceReciprocalTrialCost F l n ≤ p.eval (bitSize (comparisonInput D T U)) := by
  obtain ⟨p,hp⟩ := reciprocalVisitsCost_originalBits D F
  refine ⟨C (82+2*(4+installEncodedDigitCost F)) +
    inverseCostPolynomial (Fintype.card K) F.e + p, ?_⟩
  intro l n T U hn
  let L := bitSize (comparisonInput D T U)
  have hSize := cutInput_side_bounds D T U (show 1 ≤ l+1 by omega) hn
  have hDim : n*n^l ≤ L := by rw [←pow_succ']; exact hSize.2.1
  have hInv := loadedInverseCost_le_bits (Fintype.card K) F.e _ _ hDim
  have hVisits := hp T U hn
  have hCost : produceReciprocalTrialCost F l n ≤
      82+2*(4+installEncodedDigitCost F)+
      loadedInverseCost (Fintype.card K) F.e (n*n^l)+reciprocalVisitsCost F l n := by
    unfold produceReciprocalTrialCost reciprocalVisitsCost reciprocalVisitCost
    ring_nf
    omega
  simp only [eval_add,eval_C]
  change _ ≤ _ + _ + p.eval L
  change reciprocalVisitsCost F l n ≤ p.eval L at hVisits
  change loadedInverseCost (Fintype.card K) F.e (n*n^l) ≤ (inverseCostPolynomial (Fintype.card K) F.e).eval L at hInv
  change _ ≤ 82+2*(4+installEncodedDigitCost F)+(inverseCostPolynomial (Fintype.card K) F.e).eval L+p.eval L
  exact hCost.trans (Nat.add_le_add (Nat.add_le_add_left hInv _) hVisits)

#print axioms produceReciprocalTrial_originalBits
end EvenTI.P18Execution
