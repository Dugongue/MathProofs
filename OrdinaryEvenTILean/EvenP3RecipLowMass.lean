import EvenP3RecipLowSample
import EvenP1Condition
import EvenP1Marginal

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.Sampling Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenTI.Reciprocal.Coverage (half_independent_tuples twice_conditioned_average_le_four)
open Mathproof.EvenOrdinaryTISingular (uniformFraction uniformFraction_equiv)

noncomputable section

variable {K H L J R I B BL W : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype R] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq R]
variable [DecidableEq I] [DecidableEq B]
variable [AddCommGroup W] [Module K W]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option (J ⊕ R)) (I := I) (B := B)
local notation "V" => (Matrix I B K)
local notation "Primal" => PrimalRows K BL V
local notation "T" => (traceKernel (K := K) (I := I))
local instance : Fintype Primal := Fintype.ofFinite _

private def prodBad {a : ℕ} (g : T →ₗ[K] W) (U : BL → V) (D : Fin a × J → Ann U) : Prop :=
  ¬ Function.Surjective (quotientRows g U (fun i t => D (i,t)))

private theorem productAverage_eq {a : ℕ} (g : T →ₗ[K] W) :
    ((∑ U : BL → V, uniformFraction (Fin a × J → Ann U) (prodBad g U)) /
      (Fintype.card (BL → V) : ℝ)) =
      fiberFailureAverage (fun (U : BL → V) (D : Fin a → J → Ann U) =>
        ¬ Function.Surjective (quotientRows g U D)) := by
  unfold fiberFailureAverage
  congr 1
  apply Finset.sum_congr rfl
  intro U _
  exact uniformFraction_equiv (Equiv.curry _ _ _)
    (fun D => ¬ Function.Surjective (quotientRows g U D))

private theorem dualHalf {a : ℕ} (u : Primal)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    Nat.card (Fin a × J → Ann u.val) ≤
      2 * Nat.card {D : Fin a × J → Ann u.val // LinearIndependent K D} := by
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI : Fintype (Ann u.val) := Fintype.ofInjective Subtype.val Subtype.val_injective
  have hu : finrank K (Ann u.val) + Fintype.card BL = finrank K V := annihilator_finrank u
  exact @half_independent_tuples K (Ann u.val) (Fin a × J) _ _ _ _ _ _ (by omega)

private theorem conditionedMass_le_model {a : ℕ} (g : T →ₗ[K] W)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    ((∑ u : Primal, uniformFraction (DualRows (K := K) u.val (Fin a × J))
      (fun e => ¬ Function.Surjective (sampledQuotientRows g ⟨u,e⟩))) /
      Nat.card Primal) ≤
      4 * fiberFailureAverage (fun (U : BL → V) (D : Fin a → J → Ann U) =>
        ¬ Function.Surjective (quotientRows g U D)) := by
  letI : Fintype (Dual K V) := Fintype.ofEquiv (Matrix B I K) rectDual.toEquiv
  letI (U : BL → V) : Fintype (Fin a × J → Ann U) := Fintype.ofFinite _
  have hPrimal : Fintype.card BL + 1 ≤ finrank K V := by omega
  rw [← productAverage_eq g]
  exact twice_conditioned_average_le_four (X := BL → V) (Y := fun U => Fin a × J → Ann U)
    (fun U => LinearIndependent K U) (fun U D => LinearIndependent K D) (prodBad g)
    (half_independent_tuples (K := K) hPrimal) (fun u => dualHalf u htotal)

/-- Removing the independence conditioning in the exact physical law costs
at most four in the projected-row failure probability. -/
theorem actualSmallRows_bad_mass_le_model {a : ℕ} [Fintype Bases] [Nonempty Bases]
    (g : T →ₗ[K] W) (high : Fin a ↪ H) (low : BL ↪ L)
    (htotal : Fintype.card (Fin a × J) + Fintype.card BL + 1 ≤ finrank K V) :
    uniformFraction Bases (fun A =>
      ¬ Function.Surjective ((LinearMap.compLeft g J).comp
        (smallRows (matrixPrimal A.val.1) (matrixDual A.val.2) T (baseline_row_trace_zero A)))) ≤
      4 * fiberFailureAverage (fun (U : BL → V) (D : Fin a → J → Ann U) =>
        ¬ Function.Surjective (quotientRows g U D)) := by
  calc
    _ ≤ uniformFraction Bases (fun A =>
        ¬ Function.Surjective (sampledQuotientRows g (actualSmallRows A high low))) :=
      uniformFraction_le_of_imp (fun A h hs =>
        h (smallRows_surjective_of_actualSmallRows g A high low _ hs))
    _ = _ := uniformFraction_actualSmallRows_conditioned high low
      (fun S => ¬ Function.Surjective (sampledQuotientRows g S))
    _ ≤ _ := conditionedMass_le_model g htotal

#print axioms actualSmallRows_bad_mass_le_model

end
end Mathproof.EvenTI.Reciprocal.SquareLow
