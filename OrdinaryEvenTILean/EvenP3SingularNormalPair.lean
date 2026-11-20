import EvenP3SingularLiveCrop
import EvenNextRetainedCovariance
import Mathlib.LinearAlgebra.Matrix.Rank

namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped BigOperators TensorProduct Matrix
open Matrix Module EvenTI.Action
noncomputable section

variable {K : Type*} [Field K] {n a b k m : ℕ}

/-- Index the two physical modes of the cut, each of side n. -/
def twoModes (n : ℕ) : Fin n × Fin n ≃ Coord 2 n :=
  ((Equiv.refl (Fin n)).prodCongr
    (Equiv.funUnique (Fin 1) (Fin n)).symm).trans (retainedMode (0 : Fin 2))

def asMatrix (n : ℕ) : (Coord 2 n → K) ≃ₗ[K] Matrix (Fin n) (Fin n) K :=
  (LinearEquiv.funCongrLeft K K (twoModes n)).trans (LinearEquiv.curry K K _ _)

theorem asMatrix_rank_eq_retainedForm (ell : Coord 2 n → K) :
    (asMatrix n ell).rank = (retainedForm (0 : Fin 2) ell).rank := by
  have h : asMatrix n ell = (retainedForm (0 : Fin 2) ell).submatrix
      (Equiv.refl (Fin n)) (Equiv.funUnique (Fin 1) (Fin n)).symm := rfl
  rw [h, Matrix.rank_submatrix]

def normalPair (a k : ℕ) : Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K :=
  Matrix.fromBlocks 1 0 0 0

/-- Explicit choice of the two independent bases reducing the selected form
to the live identity and its two radicals. -/
structure NormalPair (ell : Coord 2 n → K) (a k : ℕ) where
  left : (Matrix (Fin n) (Fin n) K)ˣ
  right : (Matrix (Fin n) (Fin n) K)ˣ
  indices : Fin n ≃ Fin a ⊕ Fin k
  normalized : (left.val * asMatrix n ell * right.val).submatrix
    indices.symm indices.symm = normalPair a k

theorem normalPair_nonempty (ell : Coord 2 n → K) :
    Nonempty (NormalPair ell (asMatrix n ell).rank (n-(asMatrix n ell).rank)) := by
  obtain ⟨V,U,e,hV,hU,h⟩ := Matrix.exists_rank_normal_form (asMatrix n ell)
  obtain ⟨V,rfl⟩ := hV
  obtain ⟨U,rfl⟩ := hU
  have h' : Nonempty (NormalPair ell (asMatrix n ell).rank
      (Fintype.card (Fin n) - (asMatrix n ell).rank)) := by
    refine ⟨⟨V,U,e,?_⟩⟩
    rw [h, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
    rfl
  simpa only [Fintype.card_fin] using h'

private theorem unitT_mul_invT (P : (Matrix (Fin n) (Fin n) K)ˣ) :
    P.valᵀ * (P⁻¹).valᵀ = 1 := by
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

private theorem unitInvT_mul_T (P : (Matrix (Fin n) (Fin n) K)ˣ) :
    (P⁻¹).valᵀ * P.valᵀ = 1 := by
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

/-- Physical basis change in the dual covariant convention, preserving the
pairing of the coefficient matrix with the selected form. -/
def orient (ell : Coord 2 n → K) (P : NormalPair ell a k) :
    (Coord 2 n → K) ≃ₗ[K] Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K where
  toFun x := (((P.left⁻¹).val)ᵀ * asMatrix n x * ((P.right⁻¹).val)ᵀ).submatrix
    P.indices.symm P.indices.symm
  invFun X := (asMatrix n).symm (P.left.valᵀ * X.submatrix P.indices P.indices * P.right.valᵀ)
  left_inv x := by
    dsimp only
    rw [Matrix.submatrix_submatrix]
    simp only [Equiv.symm_comp_self, Matrix.submatrix_id_id]
    apply (asMatrix n).injective
    rw [LinearEquiv.apply_symm_apply]
    calc
      _ = (P.left.valᵀ * (P.left⁻¹).valᵀ) * asMatrix n x *
          ((P.right⁻¹).valᵀ * P.right.valᵀ) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [unitT_mul_invT, unitInvT_mul_T, Matrix.one_mul, Matrix.mul_one]
  right_inv X := by
    dsimp only
    rw [LinearEquiv.apply_symm_apply]
    have h :
        (P.left⁻¹).valᵀ * (P.left.valᵀ * X.submatrix P.indices P.indices * P.right.valᵀ) *
          (P.right⁻¹).valᵀ = X.submatrix P.indices P.indices := by
      calc
        _ = ((P.left⁻¹).valᵀ * P.left.valᵀ) * X.submatrix P.indices P.indices *
            (P.right.valᵀ * (P.right⁻¹).valᵀ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [unitInvT_mul_T, unitT_mul_invT, Matrix.one_mul, Matrix.mul_one]
    rw [h, Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id]
  map_add' x y := by simp [Matrix.mul_add, Matrix.add_mul, Matrix.submatrix_add]
  map_smul' c x := by simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.submatrix_smul]

private def liveLinear (a k : ℕ) :
    Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K →ₗ[K] CropMat K a where
  toFun X := X.submatrix Sum.inl Sum.inl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def liveProjection (ell : Coord 2 n → K) (P : NormalPair ell a k) :
    (Coord 2 n → K) →ₗ[K] CropMat K a :=
  (liveLinear a k).comp (orient ell P).toLinearMap

theorem liveProjection_surjective (ell : Coord 2 n → K) (P : NormalPair ell a k) :
    Function.Surjective (liveProjection ell P) := by
  intro X
  obtain ⟨x,hx⟩ := (orient ell P).surjective (Matrix.fromBlocks X 0 0 0)
  exact ⟨x, by rw [liveProjection, LinearMap.comp_apply, LinearEquiv.coe_coe, hx]; rfl⟩

private theorem trace_normalPair (X : Matrix (Fin a ⊕ Fin k) (Fin a ⊕ Fin k) K) :
    Matrix.trace ((normalPair a k : Matrix _ _ K)ᵀ * X) =
      Matrix.trace (X.submatrix Sum.inl Sum.inl) := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [normalPair, Matrix.fromBlocks, Matrix.one_apply]

private theorem trace_reorient (ell : Coord 2 n → K) (P : NormalPair ell a k)
    (x : Coord 2 n → K) :
    Matrix.trace ((normalPair a k : Matrix _ _ K)ᵀ * orient ell P x) =
      Matrix.trace ((asMatrix n ell)ᵀ * asMatrix n x) := by
  classical
  rw [← P.normalized]
  change Matrix.trace (((P.left.val * asMatrix n ell * P.right.val).submatrix
    P.indices.symm P.indices.symm)ᵀ *
    (((P.left⁻¹).val)ᵀ * asMatrix n x * ((P.right⁻¹).val)ᵀ).submatrix
      P.indices.symm P.indices.symm) = _
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
  have hr (A : Matrix (Fin n) (Fin n) K) :
      (A.submatrix P.indices.symm P.indices.symm).trace = A.trace := by
    change (∑ i, A (P.indices.symm i) (P.indices.symm i)) = _
    exact P.indices.symm.sum_comp (fun i => A i i)
  rw [hr, Matrix.transpose_mul, Matrix.transpose_mul]
  calc
    _ = Matrix.trace (P.right.valᵀ * (asMatrix n ell)ᵀ *
          (P.left.valᵀ * (P.left⁻¹).valᵀ) * asMatrix n x * (P.right⁻¹).valᵀ) := by
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (P.right.valᵀ * ((asMatrix n ell)ᵀ * asMatrix n x) *
          (P.right⁻¹).valᵀ) := by
      rw [unitT_mul_invT, Matrix.mul_one, Matrix.mul_assoc P.right.valᵀ]
    _ = _ := by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, unitInvT_mul_T, Matrix.one_mul]

private theorem trace_raw_dot (ell x : Coord 2 n → K) :
    Matrix.trace ((asMatrix n ell)ᵀ * asMatrix n x) = dotProductEquiv K _ ell x := by
  classical
  change (∑ i : Fin n, ∑ j : Fin n, ell (twoModes n (j,i)) * x (twoModes n (j,i))) = _
  calc
    _ = ∑ p : Fin n × Fin n, ell (twoModes n p) * x (twoModes n p) := by
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ = ∑ p : Coord 2 n, ell p * x p :=
      (twoModes n).sum_comp (fun p => ell p * x p)
    _ = _ := rfl

/-- The literal live projection has trace equal to the original raw kernel
functional, so the image has the proved codimension bound. -/
theorem liveProjection_trace (ell : Coord 2 n → K) (P : NormalPair ell a k) :
    (Matrix.traceLinearMap (α := K) (Fin a) K).comp (liveProjection ell P) =
      dotProductEquiv K _ ell := by
  apply LinearMap.ext
  intro x
  change Matrix.trace ((orient ell P x).submatrix Sum.inl Sum.inl) = _
  rw [← trace_normalPair, trace_reorient, trace_raw_dot]

end
end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.normalPair_nonempty
#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.liveProjection_trace



