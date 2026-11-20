import EvenP1ProbAssemble
import EvenP1RectTail

namespace Mathproof.EvenTI.Reciprocal.PartOne

open Matrix Module

noncomputable section

variable {K I B L J : Type*} [Field K] [Fintype K]
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [DecidableEq B]
    [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]

/-- Uniform primal matrices followed by independent uniform tuples in their
annihilator have surjective selected rows apart from mass at most q^(-n²). -/
theorem unconditioned_reciprocal_bad_le
    (hJ : Fintype.card J = Fintype.card I - 1)
    (hL : Fintype.card L = Fintype.card B / 5)
    (hI : 200 ≤ Fintype.card I) (hB : Fintype.card I^2 ≤ Fintype.card B) :
    fiberFailureAverage (fun (U : L → Matrix I B K)
      (V : Fin (Fintype.card B/5) → J → Ann U) =>
        ¬ Function.Surjective (selectedRows U V)) ≤
      1/(Fintype.card K : ℝ)^(Fintype.card I^2) := by
  apply unconditioned_selectedRows_bad_le hJ hL hI hB
  intro P hP
  have hb : Fintype.card L + Fintype.card L/2 ≤ Fintype.card B := by omega
  exact (uniformFraction_le_of_imp (fun _ h => Nat.le_of_lt h)).trans
    (Part1.uniformFraction_coefficientRank_le P hP (Fintype.card L/2) (by omega) hb)

#print axioms unconditioned_reciprocal_bad_le

end
end Mathproof.EvenTI.Reciprocal.PartOne
