import EvenP1ProbKernel
import EvenNextAnchorDense
import EvenNextRetainedCovariance

/-! Fixed nonzero vectors have the exact kernel membership probability. -/
namespace Mathproof.EvenTI.Singular.Forms

open Mathproof.EvenOrdinaryTISingular
open Mathproof.EvenTI.Reciprocal.PartOne
open EvenTI.Action Matrix Module
open scoped BigOperators Matrix

noncomputable section

variable {K I J : Type*} [Field K] [Fintype K] [Fintype I] [Fintype J] [DecidableEq J]

/-- Independently sampled rows annihilate a fixed nonzero vector with one
linear constraint per row. -/
theorem mulVec_zero_fraction (x : J → K) (hx : x ≠ 0) :
    uniformFraction (Matrix I J K) (fun A => A.mulVec x = 0) =
      1 / (Fintype.card K : ℝ) ^ Fintype.card I := by
  let f : (J → K) →ₗ[K] K := dotProductEquiv K J x
  have hf : f ≠ 0 := (dotProductEquiv K J).map_ne_zero_iff.mpr hx
  have hsur : Function.Surjective f := by
    obtain ⟨v, hv⟩ : ∃ v, f v ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (LinearMap.ext h)
    intro y
    refine ⟨(y / f v) • v, ?_⟩
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]
  have hdim : finrank K f.range = 1 := by
    rw [LinearMap.range_eq_top.mpr hsur, finrank_top, Module.finrank_self]
  let ri := Fintype.equivFin I
  let e : Matrix I J K ≃ (Fin (Fintype.card I) → J → K) :=
    { toFun := fun A i => A (ri.symm i)
      invFun := fun w i j => w (ri i) j
      left_inv := fun A => by ext i j; simp [ri]
      right_inv := fun w => by funext i j; simp [ri] }
  have he (A : Matrix I J K) : A.mulVec x = 0 ↔ ∀ i, f (e A i) = 0 := by
    constructor
    · intro h i
      have hval := congrFun h (ri.symm i)
      change (A (ri.symm i)) ⬝ᵥ x = 0 at hval
      change x ⬝ᵥ (A (ri.symm i)) = 0
      rwa [dotProduct_comm]
    · intro h
      funext i
      have hh := h (ri i)
      change x ⬝ᵥ (A (ri.symm (ri i))) = 0 at hh
      rw [Equiv.symm_apply_apply, dotProduct_comm] at hh
      exact hh
  rw [show (fun A : Matrix I J K => A.mulVec x = 0) =
      (fun A => ∀ i, f (e A i) = 0) by funext A; exact propext (he A),
    uniformFraction_equiv e (fun w => ∀ i, f (w i) = 0), zero_tuple_fraction, hdim, mul_one]

theorem rightCutKernel_zero_fraction {l r n : ℕ} (x : Coord r n → K) (hx : x ≠ 0) :
    uniformFraction (Tensor K (l+r) n) (fun T => rightCutKernel T x = 0) =
      1 / (Fintype.card K : ℝ) ^ n^l := by
  change uniformFraction (Tensor K (l+r) n) (fun T =>
    (tensorFlattenEquiv T).mulVec x = 0) = _
  rw [uniformFraction_equiv tensorFlattenEquiv (fun A => A.mulVec x = 0),
    mulVec_zero_fraction x hx, cut_side_card]

theorem leftCutKernel_zero_fraction {l r n : ℕ} (x : Coord l n → K) (hx : x ≠ 0) :
    uniformFraction (Tensor K (l+r) n) (fun T => leftCutKernel T x = 0) =
      1 / (Fintype.card K : ℝ) ^ n^r := by
  let e : Matrix (Coord l n) (Coord r n) K ≃ Matrix (Coord r n) (Coord l n) K :=
    { toFun := fun M => Mᵀ
      invFun := fun M => Mᵀ
      left_inv := Matrix.transpose_transpose
      right_inv := Matrix.transpose_transpose }
  let t := tensorFlattenEquiv.trans e
  change uniformFraction (Tensor K (l+r) n) (fun T =>
    (t T).mulVec x = 0) = _
  rw [uniformFraction_equiv t (fun A => A.mulVec x = 0), mulVec_zero_fraction x hx, cut_side_card]

#print axioms mulVec_zero_fraction
#print axioms rightCutKernel_zero_fraction
#print axioms leftCutKernel_zero_fraction
end
end Mathproof.EvenTI.Singular.Forms
