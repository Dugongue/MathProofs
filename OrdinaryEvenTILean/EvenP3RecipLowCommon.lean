import EvenP3RecipLowTail
import EvenP3RecipLowCutoff
import EvenP3RecipLowEntropy
import EvenP3RecipLowArithmetic

namespace Mathproof.EvenTI.Reciprocal.SquareLow

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.PartOne
open Mathproof.EvenOrdinaryTISingular (uniformFraction)
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K H L R I B BL : Type*} [Field K] [Fintype K] [Nonempty I]
variable [Fintype H] [Fintype L] [Fintype R] [Fintype I] [Fintype B] [Fintype BL]
variable [DecidableEq H] [DecidableEq L] [DecidableEq R]
variable [DecidableEq I] [DecidableEq B] [DecidableEq BL]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option (Fin 4 ⊕ R)) (I := I) (B := B)
local notation "T" => (traceKernel (K := K) (I := I))
local notation "b" => (Fintype.card BL)
local notation "q" => (Fintype.card K : ℝ)

def lowLabelRank (P : Matrix I I K) : ℕ :=
  finrank K (labelForm T (tracePairing P)).range

def lowFullRank (A : Bases) (P : Matrix I I K) : ℕ :=
  finrank K (squarePolar
    (deltaLinear (matrixPrimal A.val.1) (matrixDual A.val.2)) (traceBlocks (tracePairing P))).range

/-- All low labels share one good event. On this event the four retained
targets supply fifteen times each label's own restricted rank. -/
theorem square_low_common_bad_mass_le [Fintype Bases] [Nonempty Bases]
    (s : ℕ) (high : Fin b ↪ H) (low : BL ↪ L)
    (hb : 0 < b) (hB : 5*b ≤ Fintype.card B) (hI : 2 ≤ Fintype.card I) :
    uniformFraction Bases (fun A => ∃ P : Matrix I I K,
      lowLabelRank P ≤ s ∧ lowFullRank A P < 15 * lowLabelRank P) ≤
      q^(4*s+2*Fintype.card I+9) *
        (4 * q^(4*s) * (1/q^(b*(b/2)) + 1/q^(b*(b/2)))) := by
  classical
  let δ := 1 / q^(b*(b/2))
  let S := {P : Matrix I I K // lowLabelRank P ≤ s}
  letI : Fintype S := Fintype.ofFinite _
  let E (A : Bases) (P : S) := lowFullRank A P.val < 15 * lowLabelRank P.val
  have htotal : Fintype.card (Fin b × Fin 4) + b + 1 ≤ finrank K (Matrix I B K) := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, Module.finrank_matrix,
      Module.finrank_self, mul_one]
    have ht : 5*b + 1 ≤ Fintype.card I * (5*b) := by
      have hmul := Nat.mul_le_mul_right (5*b) hI
      omega
    calc
      _ = 5*b + 1 := by omega
      _ ≤ _ := ht
      _ ≤ _ := Nat.mul_le_mul_left _ hB
  have hpoint (P : S) : uniformFraction Bases (fun A => E A P) ≤ 4 * q^(4*s) * (δ+δ) := by
    have hp := actualSmallPolar_bad_mass_le (J := Fin 4) (R := R) (r := b/2)
      (tracePairing P.val) high low htotal δ (by positivity)
      (fun Z hZ => square_cut_coefficient_failure Z hZ hb hB)
    have hs := P.property
    refine (show uniformFraction Bases (fun A => E A P) ≤
      4 * q^(4*lowLabelRank P.val) * (δ+δ) by
        simpa [E, lowFullRank, lowLabelRank, δ] using hp).trans ?_
    have hq : 1 ≤ q := by exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := K)))
    have hpower : q^(4*lowLabelRank P.val) ≤ q^(4*s) :=
      pow_le_pow_right₀ hq (Nat.mul_le_mul_left 4 hs)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpower (by norm_num)) (by positivity)
  have hcard : (Fintype.card S : ℝ) ≤ q^(4*s+2*Fintype.card I+9) := by
    have hh := traceZero_label_rank_count_le (K := K) (I := I) s
    rw [Nat.card_eq_fintype_card (α := K)] at hh
    change Nat.card S ≤ _ at hh
    rw [Nat.card_eq_fintype_card] at hh
    exact_mod_cast hh
  calc
    _ ≤ uniformFraction Bases (fun A => ∃ P : S, E A P) :=
      uniformFraction_le_of_imp (fun A ⟨P, hP, he⟩ => ⟨⟨P,hP⟩,he⟩)
    _ ≤ ∑ P : S, uniformFraction Bases (fun A => E A P) := uniformFraction_exists_le _
    _ ≤ ∑ _ : S, 4 * q^(4*s) * (δ+δ) := Finset.sum_le_sum (fun P _ => hpoint P)
    _ = (Fintype.card S : ℝ) * (4 * q^(4*s) * (δ+δ)) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

#print axioms square_low_common_bad_mass_le

/-- With a square physical cut, low-label failures have total mass at most
8/q^n. The four retained targets work for every low label on the good event. -/
theorem square_low_common_bad_mass [Fintype Bases] [Nonempty Bases]
    (n s : ℕ) (hI : Fintype.card I = n) (hB : Fintype.card B = n)
    (high : Fin (n/5) ↪ H) (low : Fin (n/5) ↪ L) (hn : 1000 ≤ n)
    (hs : 1000000*s ≤ n*n) :
    uniformFraction Bases (fun A => ∃ P : Matrix I I K,
      lowLabelRank P ≤ s ∧ lowFullRank A P < 15 * lowLabelRank P) ≤ 8/q^n := by
  let e : Fin (Fintype.card (Fin (n/5))) ≃ Fin (n/5) := finCongr (Fintype.card_fin _)
  have hb : 0 < Fintype.card (Fin (n/5)) := by rw [Fintype.card_fin]; omega
  have hcardB : 5*Fintype.card (Fin (n/5)) ≤ Fintype.card B := by
    rw [hB, Fintype.card_fin]
    omega
  have hcardI : 2 ≤ Fintype.card I := by rw [hI]; omega
  have hbnd := square_low_common_bad_mass_le (K := K) (R := R) (I := I) (B := B)
    s (e.toEmbedding.trans high) low hb hcardB hcardI
  rw [Fintype.card_fin, hI] at hbnd
  have hq : 1 ≤ q := by
    exact_mod_cast (Nat.succ_le_of_lt (Fintype.card_pos (α := K)))
  exact hbnd.trans (square_low_bad_mass_numeric q hq n s _ (square_low_budget n s hn hs))

#print axioms square_low_common_bad_mass

end
end Mathproof.EvenTI.Reciprocal.SquareLow
