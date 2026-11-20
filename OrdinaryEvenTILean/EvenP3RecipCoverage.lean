import EvenP3RecipMarginalAssembly
import EvenP3RecipRegroup
import EvenP3RecipLowCommon
import EvenP3RecipHighClose

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Primary EvenTI.Action
open Mathproof.EvenTI.Reciprocal.Next Mathproof.EvenTI.Reciprocal.Four
open Mathproof.EvenTI.Reciprocal.SquareLow
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp)
open Mathproof.Problem17TracePairing (tracePairing)
open Mathproof.Problem17PolarAssembly (matAnti rank_comp_pairing rank_pullback_le)

noncomputable section

private theorem event_or_le {A : Type*} [Fintype A] (p q : A → Prop) :
    event (fun x => p x ∨ q x) ≤ event p + event q := by
  unfold event mean
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => by
    by_cases hp : p x <;> by_cases hq : q x <;> simp [hp,hq])) (by positivity)

variable {K : Type*} [Field K] [Fintype K] {n : ℕ}

local notation "Bases" => BasisPairs K (SquareRows n) (SquareCols n)
local notation "q" => (Fintype.card K : ℝ)

private theorem restrictedMatrixLabelRank_le (P : Matrix (Fin n) (Fin n) K) :
    restrictedMatrixLabelRank P ≤ finrank K (matAnti P).range := by
  calc
    _ ≤ finrank K (squarePolar LinearMap.id (tracePairing P)).range :=
      rank_pullback_le _ (traceKernel (K := K) (I := Fin n)).subtype
    _ = _ := by rw [trace_squarePolar_factor, rank_comp_pairing]

private theorem square_bad_both [Fintype Bases] [Nonempty Bases] (hn : 10^19 ≤ n) :
    event (slicedBad (highCutoff n) : Bases → Prop) ≤ 8/q^n + 16/q^(highExponent n) := by
  let s := highCutoff n
  let l (A : Bases) := ∃ P : Matrix (Fin n) (Fin n) K,
    lowLabelRank P ≤ s ∧ lowFullRank A P < 15*lowLabelRank P
  let h (A : Bases) := ∃ P : Matrix (Fin n) (Fin n) K,
    s ≤ finrank K (matAnti P).range ∧ squareHighFullRank A P < 4*n^2
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  have hB : Fintype.card (Coord 1 n) = n := by rw [cut_side_card, pow_one]
  let a : Fin (n/5) ↪ High 1 n := Fin.castLEEmb (by simp [High] <;> omega)
  let b : Fin (n/5) ↪ Low 1 n := Fin.castLEEmb (by simp [Low] <;> omega)
  have hL := square_low_common_bad_mass (K := K) (R := Fin (n-5)) (I := Fin n)
    n s (Fintype.card_fin n) hB a b (by omega)
    (by dsimp [s, highCutoff]; rw [Nat.mul_comm, pow_two]; exact Nat.div_mul_le_self _ _)
  have hH := square_high_common_bad_mass_le (K := K) (H := High 1 n) (L := Low 1 n)
    (J := SquareGroups n) (I := Fin n) (B := Coord 1 n)
    (by rwa [Fintype.card_fin]) (by rwa [Fintype.card_fin])
    (by rw [Fintype.card_fin]; exact squareGroups_card n (by omega))
    (by simp) (by simp; omega)
  rw [Fintype.card_fin] at hH
  have hu : uniformFraction Bases (slicedBad s) ≤ uniformFraction Bases (fun A => l A ∨ h A) := by
    apply uniformFraction_le_of_imp
    rintro A ⟨P, hP | hP⟩
    · exact Or.inl ⟨P,hP⟩
    · obtain ⟨hs, hr⟩ := hP
      have hr' : squareHighFullRank A P < 4*n^2 := by
        rw [Fintype.card_fin] at hr
        unfold physicalMatrixLabelRank Small.shearDelta at hr
        unfold squareHighFullRank
        convert hr using 2 <;> congr! 8
      exact Or.inr ⟨P, hs.le.trans (restrictedMatrixLabelRank_le P), hr'⟩
  simp only [← EvenTI.Singular.Coverage.event_as_fraction] at hu hL hH
  exact hu.trans ((event_or_le l h).trans (add_le_add hL hH))

abbrev squareReciprocalError (K : Type*) [Fintype K] (n : ℕ) : ℝ :=
  slicedShearError K (Fin n) (highCutoff n) +
    2 * (8/(Fintype.card K : ℝ)^n + 16/(Fintype.card K : ℝ)^(highExponent n))

/-- Actual dense reciprocal anchor marginals in order four for either cut
orientation and either retained mode in each half. -/
theorem orderFour_reciprocal_coverage (hn : 10^19 ≤ n) (i j : Fin 2) (mirror : Bool) :
    let eL := squareLeftRegroup (by omega : 5 ≤ n) i
    let eR := rightRegroup (l := 1) (n := n) j
    let orient := orientCut (K := K) (s := 2) (n := n) mirror
    (∀ [CharP K 2], marginalError (denseTraceAnchor eL eR ∘ orient) ≤ squareReciprocalError K n) ∧
    ((2 : K) ≠ 0 → marginalError (denseAnchor eL eR ∘ orient) ≤ squareReciprocalError K n) := by
  let eL := squareLeftRegroup (by omega : 5 ≤ n) i
  let eR := rightRegroup (l := 1) (n := n) j
  let orient := orientCut (K := K) (s := 2) (n := n) mirror
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty Bases := ⟨(basisPairsEquivUnits eL eR).symm 1⟩
  letI : Fintype Bases := Fintype.ofFinite _
  letI : Fintype (↥(⊤ : Submodule K (Matrix (Fin n) (Fin n) K))) := Fintype.ofFinite _
  letI : Fintype (traceKernel (K := K) (I := Fin n)) := Fintype.ofFinite _
  have hSize : 4 ≤ Fintype.card (Fin n) := by rw [Fintype.card_fin]; omega
  have hM := square_bad_both (K := K) hn
  have hF : slicedShearError K (Fin n) (highCutoff n) +
      2 * event (slicedBad (highCutoff n) : Bases → Prop) ≤ squareReciprocalError K n :=
    add_le_add_right (mul_le_mul_of_nonneg_left hM (by norm_num : 0 ≤ (2:ℝ))) _
  constructor
  · intro _
    change marginalError (denseTraceAnchor eL eR ∘ orient) ≤ _
    rw [marginalError_equiv_source]
    have he : denseTraceAnchor (K := K) eL eR =
        traceAnchor (K := K) ∘ invertibleCutEquivPairs eL eR := by
      funext T
      exact Subtype.ext (denseAnchor_eq eL eR T)
    rw [he,marginalError_equiv_source]
    exact (square_trace_marginal_of_sliced_bad_mass hSize _).trans hF
  · intro h₂
    change marginalError (denseAnchor eL eR ∘ orient) ≤ _
    have he : denseAnchor (K := K) eL eR =
        Small.anchor ∘ invertibleCutEquivPairs eL eR := funext (denseAnchor_eq eL eR)
    rw [marginalError_equiv_source, he, marginalError_equiv_source]
    exact (square_odd_marginal_of_sliced_bad_mass hSize _ h₂).trans hF

#print axioms orderFour_reciprocal_coverage

end
end Mathproof.EvenTI.Reciprocal.Coverage
