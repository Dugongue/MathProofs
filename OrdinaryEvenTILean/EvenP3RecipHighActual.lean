import EvenP3RecipHighLive
import EvenP3RecipHighModel
import EvenP3RecipHighAverage
import EvenP3RecipHighPrimal

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Classical Matrix
open Matrix Module LinearMap
open Mathproof.EvenTI.Reciprocal.Next
open Mathproof.EvenTI.Reciprocal.Sampling
open Mathproof.EvenTI.Reciprocal.PartOne (uniformFraction_le_of_imp fiberFailureAverage)
open Mathproof.EvenOrdinaryTISingular (uniformFraction uniformFraction_equiv)
open Mathproof.Problem17PolarAssembly (matAnti)
open Mathproof.Problem17TracePairing (tracePairing)

noncomputable section

variable {K H L J I B BL A C Λ : Type*} [Field K] [Fintype K]
variable [Fintype H] [Fintype L] [Fintype J] [Fintype I] [Fintype B] [Fintype BL]
variable [Fintype A] [Fintype C] [Fintype Λ]
variable [DecidableEq H] [DecidableEq L] [DecidableEq J] [DecidableEq I] [DecidableEq B]
variable [DecidableEq BL] [DecidableEq A] [DecidableEq C]

local notation "Bases" => ReciprocalBasis (K := K) (H := H) (L := L)
  (J := Option J) (I := I) (B := B)
local notation "q" => (Fintype.card K : ℝ)
local notation "n" => (Fintype.card I)
local notation "b" => (Fintype.card BL)

def splitPools {W R : Type*} {a : ℕ} (eA : A ≃ Fin a) (e : C ⊕ R ≃ J) :
    (Fin a × J → W) ≃ ((A → C → W) × (R → A → W)) where
  toFun D := (columnPool eA e D, rowPool eA e D)
  invFun p z := match e.symm z.2 with
    | .inl t => p.1 (eA.symm z.1) t
    | .inr t => p.2 t (eA.symm z.1)
  left_inv D := by
    funext z
    rcases z with ⟨a,j⟩
    change (match e.symm j with
      | .inl t => D (eA (eA.symm a),e (.inl t))
      | .inr t => D (eA (eA.symm a),e (.inr t))) = D (a,j)
    have h := e.apply_symm_apply j
    cases hj : e.symm j with
    | inl t => simp [hj] at h; simp [h]
    | inr t => simp [hj] at h; simp [h]
  right_inv p := by
    apply Prod.ext
    · funext i t
      change (match e.symm (e (.inl t)) with
        | .inl j => p.1 (eA.symm (eA i)) j
        | .inr j => p.2 j (eA.symm (eA i))) = p.1 i t
      simp
    · funext t i
      change (match e.symm (e (.inr t)) with
        | .inl j => p.1 (eA.symm (eA i)) j
        | .inr j => p.2 j (eA.symm (eA i))) = p.2 t i
      simp

abbrev squareHighFullRank (U : Bases) (P : Matrix I I K) : ℕ :=
  finrank K (squarePolar (deltaLinear (matrixPrimal U.val.1) (matrixDual U.val.2))
    (traceBlocks (tracePairing P))).range

/-- Simultaneous high-label physical rank bound, with all numerical budgets
exposed for direct substitution in the square-cut setting. -/
theorem square_high_physical_bad_mass_le [Nonempty Bases] [Fintype Bases]
    {a : ℕ} (s g d h ρ τ : ℕ) (hi : Fin a ↪ H) (lo : BL ↪ L)
    (eA : (Fin s × A) ≃ Fin a) (e : C ⊕ Fin g ≃ J)
    (P : Λ → Matrix I I K)
    (hshape : n ≤ Fintype.card B)
    (htotal : Fintype.card (Fin a × J) + b + 1 ≤ finrank K (Matrix I B K))
    (hρ : ∀ z, ρ + b + 2 * (n * d) ≤ finrank K (matAnti (P z)).range)
    (hh : h + b ≤ Fintype.card A * b)
    (hτ : τ ≤ finrank K (C → (Fin s × A) → BL → K) - n^2) :
    uniformFraction Bases (fun U => ∃ z : Λ, squareHighFullRank U (P z) < τ) ≤
      4 * (q^b * (2/q^d) +
        ((Fintype.card (Λ × (C → BL → K)) : ℝ) * ((q^(Fintype.card A * b) / q^ρ)^s) +
         (Fintype.card Λ : ℝ) * ((Nat.card (C → (Fin s × A) → BL → K) : ℝ) / q^(g*h)))) := by
  let V := Matrix I B K
  let Bad (U : BL → V) := ∃ w : BL → K, w ≠ 0 ∧ (primalCombination U w).rank < n-d
  let F (U : BL → V) (D : Fin a × J → matrixAnnihilator U) : Prop :=
    ∃ z : Λ, ∃ y : C → (Fin s × A) → BL → K, y ≠ 0 ∧
      ∀ t : Fin g, rowEvaluation (matAnti (P z)) U (columnPool eA e D) y (rowPool eA e D t) = 0
  let δ := (Fintype.card (Λ × (C → BL → K)) : ℝ) * ((q^(Fintype.card A * b) / q^ρ)^s) +
    (Fintype.card Λ : ℝ) * ((Nat.card (C → (Fin s × A) → BL → K) : ℝ) / q^(g*h))
  letI (U : BL → V) : Fintype (Fin a × J → matrixAnnihilator U) := Fintype.ofFinite _
  have hf (U : BL → V) (hg : ¬ Bad U) :
      uniformFraction (Fin a × J → matrixAnnihilator U) (F U) ≤ δ := by
    have hu (w : BL → K) (hw : w ≠ 0) : n-d ≤ (primalCombination U w).rank := by
      by_contra! hn
      exact hg ⟨w,hw,hn⟩
    have hc := matrixAnnihilator_codim U
    let eD := splitPools (W := matrixAnnihilator U) eA e
    let Q (P' : ((Fin s × A) → C → matrixAnnihilator U) × (Fin g → (Fin s × A) → matrixAnnihilator U)) :=
      ∃ z : Λ, ∃ y : C → (Fin s × A) → BL → K, y ≠ 0 ∧
        ∀ t, rowEvaluation (matAnti (P z)) U P'.1 y (P'.2 t) = 0
    change uniformFraction (Fin a × J → matrixAnnihilator U) (fun D => Q (eD D)) ≤ δ
    rw [uniformFraction_equiv eD Q]
    apply high_model_bad_mass_le s g d h ρ (fun z => matAnti (P z)) U _ hu
    · intro z
      exact (add_le_add (add_le_add le_rfl hc) le_rfl).trans (hρ z)
    · omega
  have hav := bad_fiber_average_le Bad F δ (by positivity) hf
  have hp : uniformFraction (BL → V) Bad ≤ q^b*(2/q^d) := primal_pool_rank_tail hshape d
  have ha := actual_selected_event_le_matrix_model hi lo htotal F
  have himp (U : Bases) (hu : ∃ z : Λ, squareHighFullRank U (P z) < τ) :
      F (actualRows U hi lo).1.val (liveHighDual U hi lo) := by
    obtain ⟨z,hz⟩ := hu
    by_contra hn
    have hgood (y : C → (Fin s × A) → BL → K)
        (hy : ∀ t : Fin g, rowEvaluation (matAnti (P z)) (actualRows U hi lo).1.val
          (columnPool eA e (liveHighDual U hi lo)) y (rowPool eA e (liveHighDual U hi lo) t) = 0) : y = 0 := by
      by_contra hne
      exact hn ⟨z,y,hne,hy⟩
    exact (hτ.trans (physical_rank_of_high_model_good U hi lo eA e (P z) hgood)).not_gt hz
  exact ((uniformFraction_le_of_imp himp).trans ha).trans
    (mul_le_mul_of_nonneg_left (hav.trans (add_le_add hp le_rfl)) (by norm_num))

#print axioms splitPools
#print axioms square_high_physical_bad_mass_le

end
end Mathproof.EvenTI.Reciprocal.Four