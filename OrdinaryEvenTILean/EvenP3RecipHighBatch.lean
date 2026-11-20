import EvenP3RecipHighSandwich
import EvenP3RecipHighProbability

namespace Mathproof.EvenTI.Reciprocal.Four

open scoped BigOperators Matrix
open Matrix Module LinearMap
open Mathproof.EvenOrdinaryTISingular

noncomputable section

variable {K I B A L C : Type*} [Field K]
variable [Fintype I] [Fintype B] [Fintype A] [Fintype L] [Fintype C]
variable [DecidableEq I] [DecidableEq B]

def primalCombination (U : L → Matrix I B K) (w : L → K) : Matrix I B K :=
  ∑ b, w b • U b

/-- In the high-label argument, these are the coefficients seen by one
independent reciprocal row after the column pool has been exposed. -/
def batchVector (T : Matrix I I K →ₗ[K] Matrix I I K) (U : L → Matrix I B K)
    (M : C → Matrix I B K) {W : Submodule K (Matrix B I K)}
    (V : A → C → W) (p : A × L) : Matrix I B K :=
  ∑ t, T (U p.2 * (V p.1 t).val) * M t

def evalRelation (T : Matrix I I K →ₗ[K] Matrix I I K) (U : L → Matrix I B K)
    (M : C → Matrix I B K) (W : Submodule K (Matrix B I K)) (c : A × L → K) :
    (A → C → W) →ₗ[K] Matrix I B K :=
  ∑ a : A, ∑ t : C,
    (dualSandwich (primalCombination U (fun b => c (a,b))) (M t) T).comp
      (W.subtype.comp ((LinearMap.proj t : (C → W) →ₗ[K] W).comp
        (LinearMap.proj a : (A → C → W) →ₗ[K] (C → W))))

theorem evalRelation_apply (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) (M : C → Matrix I B K)
    (W : Submodule K (Matrix B I K)) (c : A × L → K) (V : A → C → W) :
    evalRelation T U M W c V = ∑ p : A × L, c p • batchVector T U M V p := by
  simp only [evalRelation, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    Submodule.subtype_apply, dualSandwich_apply, primalCombination, batchVector,
    Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.sum_mul, Matrix.smul_mul, Matrix.mul_smul, map_sum, map_smul]

variable [DecidableEq A] [DecidableEq C]

private def oneCell (W : Submodule K (Matrix B I K)) (a : A) (t : C) :
    W →ₗ[K] (A → C → W) :=
  (LinearMap.single K (fun _ : A => C → W) a).comp
    (LinearMap.single K (fun _ : C => W) t)

theorem evalRelation_comp_cell (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) (M : C → Matrix I B K)
    (W : Submodule K (Matrix B I K)) (c : A × L → K) (a : A) (t : C) :
    (evalRelation T U M W c).comp (oneCell W a t) =
      (dualSandwich (primalCombination U (fun b => c (a,b))) (M t) T).comp W.subtype := by
  apply LinearMap.ext
  intro x
  simp only [evalRelation, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
    oneCell, LinearMap.single_apply, Submodule.subtype_apply]
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single t]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  · intro i _ hi
    simp [Pi.single_eq_of_ne hi]
  · simp

theorem evalRelation_rank (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) (M : C → Matrix I B K)
    (W : Submodule K (Matrix B I K)) (c : A × L → K) (a : A) (t : C) :
    finrank K T.range ≤ finrank K (evalRelation T U M W c).range +
      finrank K (Matrix B I K ⧸ W) +
      Fintype.card I * (Fintype.card I - (primalCombination U (fun b => c (a,b))).rank) +
      Fintype.card I * (Fintype.card I - (M t).rank) := by
  let F := dualSandwich (primalCombination U (fun b => c (a,b))) (M t) T
  have h₁ := dual_sandwich_rank (primalCombination U (fun b => c (a,b))) (M t) T
  have h₂ := precompose_rank_loss W.subtype F
  rw [Submodule.range_subtype] at h₂
  have hsum := W.finrank_quotient_add_finrank
  have h₃ := Submodule.finrank_mono
    (LinearMap.range_comp_le_range (oneCell W a t) (evalRelation T U M W c))
  rw [evalRelation_comp_cell] at h₃
  change finrank K T.range ≤ finrank K F.range + _ + _ at h₁
  change finrank K (F.comp W.subtype).range ≤ _ at h₃
  omega

variable [Fintype K]

theorem bad_column_batch_le (T : Matrix I I K →ₗ[K] Matrix I I K)
    (U : L → Matrix I B K) (M : C → Matrix I B K)
    (W : Submodule K (Matrix B I K)) (d r : ℕ)
    (hU : ∀ w : L → K, w ≠ 0 → Fintype.card I - d ≤ (primalCombination U w).rank)
    (hM : ∃ t, Fintype.card I - d ≤ (M t).rank)
    (hr : r + finrank K (Matrix B I K ⧸ W) + 2 * (Fintype.card I * d) ≤ finrank K T.range) :
    uniformFraction (A → C → W) (fun V => ¬ LinearIndependent K (batchVector T U M V)) ≤
      (Fintype.card K : ℝ)^(Fintype.card A * Fintype.card L) / (Fintype.card K : ℝ)^r := by
  classical
  letI : Fintype W := Fintype.ofFinite _
  rw [← Fintype.card_prod]
  apply dependence_fraction_le (fun V => batchVector T U M V) (evalRelation T U M W)
    (evalRelation_apply T U M W) r
  intro c hc
  have he : ∃ a : A, (fun b => c (a,b)) ≠ 0 := by
    by_contra h
    apply hc
    funext p
    have h' : (fun b => c (p.1,b)) = 0 := by
      by_contra hc'
      exact h ⟨p.1,hc'⟩
    exact congrFun h' p.2
  obtain ⟨a,ha⟩ := he
  obtain ⟨t,ht⟩ := hM
  have hrow := hU _ ha
  have h₁ : Fintype.card I - (primalCombination U (fun b => c (a,b))).rank ≤ d := by omega
  have h₂ : Fintype.card I - (M t).rank ≤ d := by omega
  have h₃ := evalRelation_rank T U M W c a t
  have h₄ := Nat.mul_le_mul_left (Fintype.card I) h₁
  have h₅ := Nat.mul_le_mul_left (Fintype.card I) h₂
  omega

#print axioms evalRelation_apply
#print axioms evalRelation_rank
#print axioms bad_column_batch_le

end
end Mathproof.EvenTI.Reciprocal.Four
