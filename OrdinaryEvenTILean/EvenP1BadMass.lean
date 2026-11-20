import EvenP1Condition
import EvenP1LawSelectedPhysical
import EvenP1ProbAverage
import EvenP1Marginal

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Classical
open Matrix Module EvenTI.Primary Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.Sampling Mathproof.EvenTI.Reciprocal.PartOne

noncomputable section

variable {K H L J I B BL : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J]
variable [DecidableEq I] [DecidableEq B] [DecidableEq BL] [Nonempty I]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "a" => (Fintype.card B / 5)
local notation "V" => (Matrix I B K)

private theorem selected_dimensions
    (hJ : Fintype.card J = Fintype.card I - 1)
    (hL : Fintype.card BL = a) (hI : 200 ≤ Fintype.card I)
    (hB : Fintype.card I^2 ≤ Fintype.card B) :
    Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V := by
  have hm : 0 < Fintype.card B := by
    have : 0 < Fintype.card I ^ 2 := by positivity
    omega
  have ha : a + 1 ≤ Fintype.card B := by omega
  have hj : Fintype.card J + 1 = Fintype.card I := by omega
  rw [Module.finrank_matrix, Module.finrank_self, mul_one, Fintype.card_prod,
    Fintype.card_fin, hL]
  calc
    _ ≤ (a+1) * (Fintype.card J + 1) := by
      simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
      omega
    _ ≤ _ := by rw [hj, Nat.mul_comm (Fintype.card I)]; exact Nat.mul_le_mul_right _ ha

local notation "Primal" => PrimalRows K BL V
local instance massPrimalFintype : Fintype Primal := Fintype.ofFinite _

private def modelMass : ℝ :=
  fiberFailureAverage (fun (U : BL → V) (W : Fin a → J → Ann U) =>
    ¬ Function.Surjective (selectedRows U W))

private def conditionedMass : ℝ :=
  (∑ u : Primal, uniformFraction (DualRows (K := K) u.val (Fin a × J))
    (fun e => ¬ Function.Surjective (sampledSelectedRows ⟨u,e⟩))) / Nat.card Primal

private theorem selectedBad_le_conditioned [Fintype Bases] [Nonempty Bases]
    (high : Fin a ↪ H) (low : BL ↪ L) :
    event (fun A : Bases => ¬ Function.Surjective (Next.baselineRows A)) ≤
      conditionedMass (K := K) (I := I) (B := B) (BL := BL) (J := J) := by
  rw [event_eq_card]
  change uniformFraction Bases _ ≤ _
  calc
    _ ≤ uniformFraction Bases (fun A => ¬ Function.Surjective
        (sampledSelectedRows (actualRows A high low))) :=
      uniformFraction_le_of_imp (fun A h h' =>
        h (baselineRows_surjective_of_actualRows A high low h'))
    _ = _ := uniformFraction_actualRows_conditioned high low
      (fun S => ¬ Function.Surjective (sampledSelectedRows S))

private def prodBad (U : BL → V) (D : Fin a × J → Ann U) : Prop :=
  ¬ Function.Surjective (selectedRows U (fun i t => D (i,t)))

private def prodMass : ℝ :=
  (∑ U : BL → V, uniformFraction (Fin a × J → Ann U) (prodBad U)) /
    (Fintype.card (BL → V) : ℝ)

private theorem prodMass_eq :
    prodMass (K := K) (I := I) (B := B) (BL := BL) (J := J) =
      modelMass (K := K) (I := I) (B := B) (BL := BL) (J := J) := by
  unfold prodMass modelMass fiberFailureAverage
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  exact uniformFraction_equiv (Equiv.curry _ _ _)
    (fun W => ¬ Function.Surjective (selectedRows U W))

private theorem dualHalf (u : Primal)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    Nat.card (Fin a × J → Ann u.val) ≤
      2 * Nat.card {D : Fin a × J → Ann u.val // LinearIndependent K D} := by
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI : Fintype (Ann u.val) := Fintype.ofInjective Subtype.val Subtype.val_injective
  have hu : finrank K (Ann u.val) + Fintype.card BL = finrank K V := annihilator_finrank u
  exact @half_independent_tuples K (Ann u.val) (Fin a × J) _ _ _ _ _ _ (by omega)

private theorem conditionedMass_le_prod
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    conditionedMass (K := K) (I := I) (B := B) (BL := BL) (J := J) ≤
      4 * prodMass (K := K) (I := I) (B := B) (BL := BL) (J := J) := by
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI (U : BL → V) : Fintype (Fin a × J → Ann U) := Fintype.ofFinite _
  have hPrimal : Fintype.card BL + 1 ≤ finrank K V := by omega
  exact twice_conditioned_average_le_four (X := BL → V) (Y := fun U => Fin a × J → Ann U)
    (fun U => LinearIndependent K U) (fun U D => LinearIndependent K D) prodBad
    (half_independent_tuples (K := K) hPrimal) (fun u => dualHalf u htotal)

theorem actual_reciprocal_bad_mass_le_model [Fintype Bases] [Nonempty Bases]
    (high : Fin a ↪ H) (low : BL ↪ L)
    (hJ : Fintype.card J = Fintype.card I - 1)
    (hL : Fintype.card BL = a) (hI : 200 ≤ Fintype.card I)
    (hB : Fintype.card I^2 ≤ Fintype.card B) :
    event (fun A : Bases => ¬ Function.Surjective (Next.baselineRows A)) ≤
      4 * fiberFailureAverage
        (fun (U : BL → V) (W : Fin a → J → Ann U) =>
          ¬ Function.Surjective (selectedRows U W)) :=
  (selectedBad_le_conditioned high low).trans
    ((conditionedMass_le_prod (selected_dimensions (K := K) hJ hL hI hB)).trans_eq
      (congrArg (fun z : ℝ => 4*z) prodMass_eq))

#print axioms actual_reciprocal_bad_mass_le_model

end
end Mathproof.EvenTI.Reciprocal.Coverage
