import EvenP2FormsKernel

/-! Full retained rank is typical among uniformly sampled dense forms. -/
namespace Mathproof.EvenTI.Singular.Forms

open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne
open EvenTI.Action Matrix Module
open scoped BigOperators Matrix

noncomputable section

variable {K I J : Type*} [Field K] [Fintype K] [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J]

private def transposeEquiv' : Matrix I J K ≃ Matrix J I K where
  toFun M := Mᵀ
  invFun M := Mᵀ
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose

theorem rank_bad_nonzero_left (A : Matrix I J K) (h : A.rank ≠ Fintype.card I) :
    ∃ x : {x : I → K // x ≠ 0}, Aᵀ.mulVec x.val = 0 := by
  have hn : ¬ Function.Surjective A.toLin' := by
    intro hs
    apply h
    change finrank K A.toLin'.range = Fintype.card I
    rw [LinearMap.range_eq_top.mpr hs, finrank_top, Module.finrank_fintype_fun_eq_card]
  obtain ⟨z, hz, hcomp⟩ := (not_surjective_iff_dual A.toLin').mp hn
  let x := (dotProductEquiv K I).symm z
  have hx : x ≠ 0 := (dotProductEquiv K I).symm.map_ne_zero_iff.mpr hz
  refine ⟨⟨x, hx⟩, ?_⟩
  have hdual : A.toLin'.dualMap z = 0 := hcomp
  rw [← (dotProductEquiv K I).apply_symm_apply z, dualMap_dotProductEquiv] at hdual
  exact (dotProductEquiv K J).map_eq_zero_iff.mp hdual

/-- Rectangular failure is controlled by a union over nonzero left null
vectors. This bound is valid in all finite fields. -/
theorem rank_bad_fraction :
    uniformFraction (Matrix I J K) (fun A => A.rank ≠ Fintype.card I) ≤
      (Fintype.card K : ℝ) ^ Fintype.card I / (Fintype.card K : ℝ) ^ Fintype.card J := by
  classical
  let X := {x : I → K // x ≠ 0}
  have hcount : Fintype.card X ≤ Fintype.card K ^ Fintype.card I := by
    rw [← Fintype.card_fun]
    exact Fintype.card_le_of_injective (fun x : X => x.val) Subtype.val_injective
  have hterm (x : X) :
      uniformFraction (Matrix I J K) (fun A => Aᵀ.mulVec x.val = 0) =
        1 / (Fintype.card K : ℝ) ^ Fintype.card J := by
    rw [show (fun A : Matrix I J K => Aᵀ.mulVec x.val = 0) =
        (fun A => (transposeEquiv' A).mulVec x.val = 0) by rfl,
      uniformFraction_equiv transposeEquiv' (fun A => A.mulVec x.val = 0),
      mulVec_zero_fraction _ x.property]
  calc
    _ ≤ uniformFraction (Matrix I J K) (fun A => ∃ x : X, Aᵀ.mulVec x.val = 0) :=
      uniformFraction_le_of_imp rank_bad_nonzero_left
    _ ≤ ∑ x : X, uniformFraction (Matrix I J K) (fun A => Aᵀ.mulVec x.val = 0) :=
      uniformFraction_exists_le _
    _ = (Fintype.card X : ℝ) / (Fintype.card K : ℝ) ^ Fintype.card J := by
      simp [hterm, div_eq_mul_inv, nsmul_eq_mul]
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast hcount

/-- Retaining a physical mode is a coordinate permutation on dense forms. -/
def retainedFormEquiv {l n : ℕ} (i : Fin (l+1)) :
    (Coord (l+1) n → K) ≃ Matrix (Fin n) (Coord l n) K where
  toFun := retainedForm i
  invFun A z := A ((retainedMode i).symm z).1 ((retainedMode i).symm z).2
  left_inv := by
    intro t
    funext z
    change t (retainedMode i ((retainedMode i).symm z)) = t z
    rw [Equiv.apply_symm_apply]
  right_inv := by
    intro A
    ext x y
    change A ((retainedMode i).symm (retainedMode i (x,y))).1
      ((retainedMode i).symm (retainedMode i (x,y))).2 = _
    rw [Equiv.symm_apply_apply]

theorem all_retained_bad_fraction {l n : ℕ} :
    uniformFraction (Coord (l+1) n → K)
      (fun x => ∃ i, (retainedForm i x).rank ≠ n) ≤
      (l+1 : ℝ) * ((Fintype.card K : ℝ)^n / (Fintype.card K : ℝ)^(n^l)) := by
  have h (i : Fin (l+1)) :
      uniformFraction (Coord (l+1) n → K) (fun x => (retainedForm i x).rank ≠ n) ≤
        (Fintype.card K : ℝ)^n / (Fintype.card K : ℝ)^(n^l) := by
    change uniformFraction (Coord (l+1) n → K)
      (fun x => (retainedFormEquiv i x).rank ≠ n) ≤ _
    rw [uniformFraction_equiv (retainedFormEquiv i) (fun A => A.rank ≠ n)]
    simpa only [Fintype.card_fin, cut_side_card] using
      (rank_bad_fraction (I := Fin n) (J := Coord l n) (K := K))
  calc
    _ ≤ ∑ i : Fin (l+1), uniformFraction (Coord (l+1) n → K)
        (fun x => (retainedForm i x).rank ≠ n) := uniformFraction_exists_le _
    _ ≤ ∑ _i : Fin (l+1), (Fintype.card K : ℝ)^n / (Fintype.card K : ℝ)^(n^l) :=
      Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by simp [nsmul_eq_mul, Nat.cast_add]

#print axioms rank_bad_fraction
#print axioms all_retained_bad_fraction
end
end Mathproof.EvenTI.Singular.Forms
