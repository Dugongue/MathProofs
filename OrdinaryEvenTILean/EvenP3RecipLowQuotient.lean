import EvenP1ProbAverage
import EvenP1ProbLabel

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open Matrix Module LinearMap
open scoped BigOperators
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.Next (traceKernel)
open Mathproof.EvenTI.Reciprocal.PartOne

noncomputable section

private theorem pointwise_surj {K J T W : Type*} [Field K]
    [AddCommGroup T] [Module K T] [AddCommGroup W] [Module K W]
    (g : T →ₗ[K] W) (hg : Function.Surjective g) :
    Function.Surjective (LinearMap.compLeft g J) := by
  intro y
  choose x hx using fun j => hg (y j)
  exact ⟨x, funext hx⟩

variable {K I B L J W : Type*} [Field K] [Fintype K]
    [Fintype I] [DecidableEq I] [Nonempty I] [Fintype B] [DecidableEq B]
    [Fintype L] [DecidableEq L] [Fintype J] [DecidableEq J]
    [AddCommGroup W] [Module K W] [Fintype W]

local notation "T" => (traceKernel (K := K) (I := I))
local notation "UType" => (L → Matrix I B K)
local notation "Labels" => {z : Dual K (J → W) // z ≠ 0}

def quotientRows (g : T →ₗ[K] W) {a : ℕ} (U : UType) (V : Fin a → J → Ann U) :
    (Fin a → L → K) →ₗ[K] (J → W) :=
  (LinearMap.compLeft g J).comp (selectedRows U V)

private def liftLabel (g : T →ₗ[K] W) (z : Labels) : Dual K (J → T) :=
  z.val.comp (LinearMap.compLeft g J)

private theorem liftLabel_ne_zero (g : T →ₗ[K] W) (hg : Function.Surjective g)
    (z : Labels) : liftLabel g z ≠ 0 := by
  intro h
  apply z.property
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := pointwise_surj (J := J) g hg y
  exact LinearMap.congr_fun h x

private def annFintype (U : UType) : Fintype (J → Ann U) := by
  letI : Fintype (Dual K (Matrix I B K)) :=
    Fintype.ofEquiv (Matrix B I K) (rectDual (K := K) (I := I) (B := B)).toEquiv
  exact Fintype.ofInjective (fun (v : J → Ann U) t => (v t).val) (by
    intro x y hxy
    funext t
    exact Subtype.ext (congrFun hxy t))

private theorem label_rank_cutoff (g : T →ₗ[K] W) (hg : Function.Surjective g)
    {r : ℕ} {δ : ℝ} (z : Labels)
    (hRank : ∀ P : Matrix I I K, (∀ c : K, P ≠ c • 1) →
      uniformFraction UType (fun U => Part1.coefficientRank P U < r) ≤ δ) :
    uniformFraction UType (fun U => finrank K (coeff (liftLabel g z) U).range < r) ≤ δ := by
  obtain ⟨t, P, hn, ht⟩ := exists_nonscalar_component (liftLabel g z) (liftLabel_ne_zero g hg z)
  exact (uniformFraction_le_of_imp (fun U h =>
    lt_of_le_of_lt (coeff_rank_ge_of_component (liftLabel g z) U t P ht) h)).trans (hRank P hn)

set_option maxHeartbeats 250000 in
/-- The square-cut law needs surjectivity only after the label-dependent
projection. The failure estimate depends on the projected dimension. -/
theorem unconditioned_quotientRows_bad_le {a r : ℕ} (g : T →ₗ[K] W)
    (hg : Function.Surjective g) [Fintype Labels] (δ : ℝ)
    (hRank : ∀ P : Matrix I I K, (∀ c : K, P ≠ c • 1) →
      uniformFraction UType (fun U => Part1.coefficientRank P U < r) ≤ δ) :
    fiberFailureAverage (fun (U : UType) (V : Fin a → J → Ann U) =>
      ¬ Function.Surjective (quotientRows g U V)) ≤
      (Fintype.card Labels : ℝ) * (δ + 1 / (Fintype.card K : ℝ)^(a*r)) := by
  classical
  letI : ∀ U : UType, Fintype (J → Ann U) := annFintype
  letI : ∀ U : UType, AddCommGroup (J → Ann U) := fun _ => inferInstance
  letI : ∀ U : UType, Module K (J → Ann U) := fun _ => inferInstance
  exact average_nonsurjective_le_of_cutoff (K := K)
    (X := UType) (V := fun U => J → Ann U)
    (W := J → W) (Z := L → K) (D := Fin a → L → K) (a := a)
    (fun U V => quotientRows g U V)
    (fun z U => coeff (liftLabel g z) U)
    (fun z U V hkill => coeff_zero_of_comp_zero (liftLabel g z) U V (by
      change (z.val.comp (LinearMap.compLeft g J)).comp (selectedRows U V) = 0
      rwa [LinearMap.comp_assoc]))
    r δ (fun z => label_rank_cutoff g hg z hRank)

#print axioms unconditioned_quotientRows_bad_le

end
end Mathproof.EvenTI.Reciprocal.SquareLow
