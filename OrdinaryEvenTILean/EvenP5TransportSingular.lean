import EvenP2CropAnchors

namespace Mathproof.EvenOrdinaryTISingular

open scoped Matrix TensorProduct
open Matrix Module EvenTI.Action EvenTI.AnchorCovariance
noncomputable section

variable {K : Type*} [Field K] {l r n : ℕ}

/-- In standard coordinates the physical kernel projection is ordinary
matrix multiplication by the transposed retained form. -/
theorem physicalMatrixProjection_apply_eq
    (i : Fin (l + 1)) (ell x : Coord (l + 1) n → K) :
    physicalMatrixProjection i ell x = retainedForm i x * (retainedForm i ell)ᵀ := by
  let f : (Coord (l + 1) n → K) →ₗ[K] PhysicalMatrix K n :=
    { toFun := fun z => retainedForm i z * (retainedForm i ell)ᵀ
      map_add' := by
        intro u v
        have h : retainedForm i (u + v) = retainedForm i u + retainedForm i v := by
          ext a b
          rfl
        rw [h, Matrix.add_mul]
      map_smul' := by
        intro c u
        have h : retainedForm i (c • u) = c • retainedForm i u := by
          ext a b
          rfl
        rw [h, Matrix.smul_mul] <;> rfl }
  change physicalMatrixProjection i ell x = f x
  suffices h : physicalMatrixProjection i ell = f by rw [h]
  apply (Pi.basisFun K (Coord (l + 1) n)).ext
  intro z
  obtain ⟨⟨a, b⟩, rfl⟩ := (retainedMode i).surjective z
  let X := (Pi.basisFun K (Coord (l + 1) n)) (retainedMode i (a,b))
  let B := Pi.basisFun K (Fin n)
  let C := Pi.basisFun K (Coord l n)
  have hreg : regroupCoordinates i X = B a ⊗ₜ[K] C b := by
    apply (regroupCoordinates i).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact (regroupCoordinates_inverse_basis i a b).symm
  have hell (c : Fin n) : regroupKernelForm i ell (B c ⊗ₜ[K] C b) = retainedForm i ell c b := by
    change (dotProductEquiv K _ ell) ((regroupCoordinates i).symm (B c ⊗ₜ[K] C b)) = _
    rw [regroupCoordinates_inverse_basis]
    change ell ⬝ᵥ (Pi.basisFun K _ (retainedMode i (c,b))) = _
    rw [Pi.basisFun_apply, dotProduct_single_one]
    rfl
  ext d c
  change ((physicalEndMatrix K n) (kernelProjection (regroupKernelForm i ell)
    (regroupCoordinates i X))) d c = (retainedForm i X * (retainedForm i ell)ᵀ) d c
  rw [physicalEndMatrix, LinearMap.toMatrix_apply, Pi.basisFun_repr, hreg]
  change kernelProjection (regroupKernelForm i ell) (B a ⊗ₜ[K] C b) (B c) d = _
  rw [kernelProjection_tmul, hell]
  let Y : Coord l n → K := Pi.single b (B a d)
  have hrow : retainedForm i X d = Y := by
    funext y
    change (Pi.basisFun K _ (retainedMode i (a,b))) (retainedMode i (d,y)) = Y y
    by_cases ha : a = d <;> by_cases hb : b = y <;>
      simp [Y, B, Pi.basisFun_apply, Pi.single_apply, (retainedMode i).injective.eq_iff,
        Prod.mk.injEq, ha, hb, eq_comm, Ne.symm]
  change retainedForm i ell c b * B a d = retainedForm i X d ⬝ᵥ retainedForm i ell c
  rw [hrow, show Y = (Pi.single b (B a d) : Coord l n → K) from rfl,
    single_dotProduct, mul_comm]

private theorem physicalMatrixProjection_move
    (i : Fin (l + 1)) (g : Changes K (l + 1) n) (ell x : Coord (l + 1) n → K) :
    physicalMatrixProjection i (moveCutForm (productUnit g) ell) (act g x) =
      (g i).val * physicalMatrixProjection i ell x * (g i).inv := by
  let A := retainedForm i x
  let B := retainedForm i ell
  let P := g i
  let Q := productUnit (fun j => g (i.succAbove j))
  have hmove : moveCutForm (productUnit g) ell = act (dualChanges g) ell := by
    rw [act, dual_product]
    rfl
  have hp : retainedForm i (act g x) = P.val * A * Q.valᵀ :=
    retainedForm_act i g x
  have hq : retainedForm i (moveCutForm (productUnit g) ell) =
      P.invᵀ * B * Q.inv := by
    rw [hmove, retainedForm_act]
    rfl
  rw [physicalMatrixProjection_apply_eq, physicalMatrixProjection_apply_eq, hp, hq,
    Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hcancel : Q.valᵀ * Q.invᵀ = 1 := by
    rw [← Matrix.transpose_mul, Q.inv_val, Matrix.transpose_one]
  calc
    _ = P.val * A * (Q.valᵀ * Q.invᵀ) * Bᵀ * P.inv := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcancel, Matrix.mul_one, Matrix.mul_assoc P.val A]

private def matrixConj (P : (PhysicalMatrix K n)ˣ) :
    PhysicalMatrix K n →ₗ[K] PhysicalMatrix K n where
  toFun A := P.val * A * P.inv
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rfl

private theorem matrixConj_tensor
    (P Q : (PhysicalMatrix K n)ˣ) (Z : PhysicalMatrix K n ⊗[K] PhysicalMatrix K n) :
    kroneckerLinearEquiv (Fin n) (Fin n) (Fin n) (Fin n) K
        (TensorProduct.map (matrixConj P) (matrixConj Q) Z) =
      kronecker P.val Q.val * kroneckerLinearEquiv _ _ _ _ K Z * kronecker P.inv Q.inv := by
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | tmul A B =>
    simp only [TensorProduct.map_tmul, kroneckerLinearEquiv_tmul]
    change Matrix.kronecker (P.val * A * P.inv) (Q.val * B * Q.inv) = _
    unfold Matrix.kronecker
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]
  | add A B hA hB =>
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, hA, hB]

private theorem literalSingularProjection_act
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : Tensor K ((l + 1) + (r + 1)) n) (g : Changes K ((l + 1) + (r + 1)) n) :
    literalSingularProjection i j (moveLeftForm g ell) (moveRightForm g rho) (act g A) =
      TensorProduct.map (matrixConj (leftModes g i)) (matrixConj (rightModes g j))
        (literalSingularProjection i j ell rho A) := by
  have hproj {s : ℕ} (k : Fin (s + 1)) (h : Changes K (s + 1) n)
      (f : Coord (s + 1) n → K) :
      (physicalMatrixProjection k (moveCutForm (productUnit h) f)).comp
          (productMatrix h).toLin' =
        (matrixConj (h k)).comp (physicalMatrixProjection k f) := by
    apply LinearMap.ext
    intro z
    exact physicalMatrixProjection_move k h f z
  unfold literalSingularProjection
  rw [flatten_action, ← matrixTensorEquiv_matrix_mul, TensorProduct.map_map, TensorProduct.map_map]
  rw [moveLeftForm, moveRightForm, hproj, hproj]

/-- The actual paired singular anchors move by the corresponding physical
conjugations for arbitrary raw forms, including rank-deficient forms. -/
theorem literalSingularAnchors_act
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : Tensor K ((l + 1) + (r + 1)) n) (g : Changes K ((l + 1) + (r + 1)) n) :
    literalSingularAnchors i j (moveLeftForm g ell) (moveRightForm g rho) (act g A) =
      ((leftModes g i).val * (literalSingularAnchors i j ell rho A).1 * (leftModes g i).inv,
       (rightModes g j).val * (literalSingularAnchors i j ell rho A).2 * (rightModes g j).inv) := by
  let P := leftModes g i
  let Q := rightModes g j
  let Z := kroneckerLinearEquiv (Fin n) (Fin n) (Fin n) (Fin n) K
    (literalSingularProjection i j ell rho A)
  unfold literalSingularAnchors
  rw [literalSingularProjection_act, matrixConj_tensor]
  exact Prod.ext (quadratic_covariant Z P.val P.inv Q.val Q.inv P.inv_val Q.inv_val).1
    (quadratic_covariant Z P.val P.inv Q.val Q.inv P.inv_val Q.inv_val).2

/-- Tests using only the actual anchor characteristic polynomials accept a
transporter exactly when they accept the source. -/
theorem literalSingularAnchors_charpolys_act
    (i : Fin (l + 1)) (j : Fin (r + 1))
    (ell : Coord (l + 1) n → K) (rho : Coord (r + 1) n → K)
    (A : Tensor K ((l + 1) + (r + 1)) n) (g : Changes K ((l + 1) + (r + 1)) n) :
    Prod.map Matrix.charpoly Matrix.charpoly
        (literalSingularAnchors i j (moveLeftForm g ell) (moveRightForm g rho) (act g A)) =
      Prod.map Matrix.charpoly Matrix.charpoly (literalSingularAnchors i j ell rho A) := by
  rw [literalSingularAnchors_act]
  apply Prod.ext
  · change ((leftModes g i).val * _ * (leftModes g i).inv).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_val, Matrix.one_mul] <;> rfl
  · change ((rightModes g j).val * _ * (rightModes g j).inv).charpoly = _
    rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Units.inv_val, Matrix.one_mul] <;> rfl

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.physicalMatrixProjection_apply_eq
#print axioms Mathproof.EvenOrdinaryTISingular.literalSingularAnchors_act
#print axioms Mathproof.EvenOrdinaryTISingular.literalSingularAnchors_charpolys_act
