import EvenP3RecipShearBudget
import EvenP3RecipLabelChoice
import EvenP3SlicedFourierMass
import EvenP3RecipLowEntropy

namespace Mathproof.EvenTI.Reciprocal.Coverage

open scoped BigOperators Matrix Classical
open Matrix Module EvenTI.Primary Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.OrderFour Mathproof.EvenTI.Reciprocal.SquareLow
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K H L J I B : Type*} [Field K] [Fintype K] [Nonempty I]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L) (J := Option J) (I := I) (B := B)
local notation "Shear" => UpperShear K H L (Option J)
local notation "n" => Fintype.card I
local notation "q" => (Fintype.card K : ℝ)

def restrictedMatrixLabelRank (P : Matrix I I K) : ℕ :=
  finrank K (labelForm traceKernel (tracePairing P)).range

def physicalMatrixLabelRank (A : Bases) (P : Matrix I I K) : ℕ :=
  finrank K (squarePolar (Small.shearDelta A) (traceBlocks (tracePairing P))).range

/-- The finite low/high rank estimates for one physical basis combine
before averaging over reciprocal bases. -/
theorem square_reciprocal_shear_l1_of_good_label_ranks (A : Bases) (hn : 4 ≤ n)
    (S : Submodule K (Matrix I I K)) [Fintype S] [Fintype (Module.Dual K S)]
    (hS : ∀ X : Shear, Small.anchor (applyShear X A) - Small.anchor A ∈ S)
    (ψ : AddChar K ℂ) (hψ : ψ ≠ 1) (s : ℕ)
    (hMin : ∀ c : Module.Dual K S, c ≠ 0 → n-2 ≤ restrictedMatrixLabelRank (matrixLabelChoice S c))
    (hLow : ∀ P : Matrix I I K, restrictedMatrixLabelRank P ≤ s →
      15 * restrictedMatrixLabelRank P ≤ physicalMatrixLabelRank A P)
    (hHigh : ∀ P : Matrix I I K, s < restrictedMatrixLabelRank P →
      4*n^2 ≤ physicalMatrixLabelRank A P) :
    marginalError (fun X : Shear => (⟨Small.anchor (applyShear X A) - Small.anchor A, hS X⟩ : S)) ≤
      Real.sqrt ((↑(s+1) : ℝ) * (q^(9*n-31))⁻¹ + (q^(n^2)) * (q^(4*n^2))⁻¹) := by
  let e := matrixLabelChoice S
  let d := restrictedMatrixLabelRank ∘ e
  let r := physicalMatrixLabelRank A ∘ e
  let p := (↑(s+1) : ℝ) * (q^(9*n-31))⁻¹ + (q^(n^2)) * (q^(4*n^2))⁻¹
  have hq : 1 ≤ q := by exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := K)))
  have hCard : (Fintype.card (Module.Dual K S) : ℝ) ≤ q^(n^2) := by
    rw [← Nat.cast_pow]
    exact_mod_cast (show Fintype.card (Module.Dual K S) ≤ Fintype.card K ^ n^2 by
      have h := Fintype.card_le_of_injective e e.injective
      change Fintype.card (Module.Dual K S) ≤ Fintype.card (I → I → K) at h
      rwa [Fintype.card_fun, Fintype.card_fun, ← pow_mul, ← pow_two] at h)
  have hCount (j : ℕ) : ((Finset.univ.filter (fun c => d c = j)).card : ℝ) ≤ q^(4*j+(2*n+9)) := by
    let f (c : {c : Module.Dual K S // d c = j}) : {P : Matrix I I K // restrictedMatrixLabelRank P ≤ j} :=
      ⟨e c.val, c.property.le⟩
    have hi : Function.Injective f := fun x y h => Subtype.ext (e.injective (congrArg Subtype.val h))
    have h := (Nat.card_le_card_of_injective f hi).trans (traceZero_label_rank_count_le (K := K) (I := I) j)
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.card_eq_fintype_card (α := K),
      Nat.add_assoc] at h
    exact_mod_cast h
  refine reciprocal_shear_l1_of_label_budget A S hS ψ hψ r (Real.sqrt p)
    (Real.sqrt_nonneg _) (fun m _ => ⟨tracePairing (e m), matrixLabelChoice_spec S m, le_rfl⟩) ?_
  rw [Real.sq_sqrt (by dsimp [p]; positivity : 0 ≤ p)]
  apply split_label_mass_le q hq d r s 4 (2*n+9) (9*n-31) (4*n^2) _ hCard hCount
  · intro c hc hsmall
    have hm := hMin c hc
    have hr := hLow (e c) hsmall
    change n-2 ≤ d c at hm
    change 15*d c ≤ r c at hr
    omega
  · intro c _ hlarge
    exact hHigh (e c) hlarge

#print axioms square_reciprocal_shear_l1_of_good_label_ranks

end
end Mathproof.EvenTI.Reciprocal.Coverage
