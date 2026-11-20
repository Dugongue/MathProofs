import EvenP1LawSelectedPhysical
import EvenP1Condition
import EvenP1ProbAverage
import EvenP3RecipHighAnnihilator

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenTI.Reciprocal.Sampling
open Mathproof.EvenTI.Reciprocal.Coverage (half_independent_tuples twice_conditioned_average_le_four)
open Mathproof.EvenOrdinaryTISingular (uniformFraction uniformFraction_equiv)

noncomputable section

variable {K H L J I B BL : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]
variable [DecidableEq BL]

local notation "Bases" =>
  ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "V" => (Matrix I B K)
local notation "Prim" => (PrimalRows K BL (Matrix I B K))

private instance primalFintype : Fintype Prim := Fintype.ofFinite _

private theorem dual_half {a : ℕ} (u : Prim)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    Nat.card (Fin a × J → Ann u.val) ≤
      2 * Nat.card {D : Fin a × J → Ann u.val // LinearIndependent K D} := by
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI : Fintype (Ann u.val) := Fintype.ofInjective Subtype.val Subtype.val_injective
  have hu : finrank K (Ann u.val) + Fintype.card BL = finrank K V := annihilator_finrank u
  exact @half_independent_tuples K (Ann u.val) (Fin a × J) _ _ _ _ _ _ (by omega)

/-- Transfer any bad event in a selected reciprocal sample from the uniform
physical basis to the concrete two-stage unconditioned matrix model. -/
theorem actual_selected_event_le_matrix_model {a : ℕ} [Nonempty Bases]
    (hi : Fin a ↪ H) (lo : BL ↪ L)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V)
    (P : ∀ U : BL → V, (Fin a × J → matrixAnnihilator U) → Prop) :
    uniformFraction Bases (fun A => P (actualRows A hi lo).1.val
      (fun g => (matrixAnnihilatorEquiv (actualRows A hi lo).1.val).symm
        ((actualRows A hi lo).2.val g))) ≤
      4 * fiberFailureAverage P := by
  classical
  let E (U : BL → V) (D : Fin a × J → Ann U) : Prop :=
    P U (fun g => (matrixAnnihilatorEquiv U).symm (D g))
  rw [uniformFraction_actualRows_conditioned hi lo
    (fun A => E A.1.val A.2.val)]
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI (U : BL → V) : Fintype (Fin a × J → Ann U) := Fintype.ofFinite _
  have hPrimal : Fintype.card BL + 1 ≤ finrank K V := by omega
  have h := twice_conditioned_average_le_four (X := BL → (Matrix I B K))
    (Y := fun U => Fin a × J → Ann U) (fun U => LinearIndependent K U)
    (fun U D => LinearIndependent K D) E (half_independent_tuples (K := K) hPrimal)
    (fun u => dual_half u htotal)
  refine h.trans_eq ?_
  congr 1
  unfold fiberFailureAverage
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  exact uniformFraction_equiv (Equiv.arrowCongr (Equiv.refl (Fin a × J))
    (matrixAnnihilatorEquiv U).symm.toEquiv) (P U)

#print axioms actual_selected_event_le_matrix_model

end
end Mathproof.EvenTI.Reciprocal.Four