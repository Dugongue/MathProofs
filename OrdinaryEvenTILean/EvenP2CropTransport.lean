import EvenP2CropTensor

namespace Mathproof.EvenOrdinaryTISingular
open scoped Matrix TensorProduct
open Matrix Module
noncomputable section

variable {K M N I J : Type*} [Field K]
  [Fintype M] [Fintype N] [Fintype I] [Fintype J]
  [DecidableEq M] [DecidableEq N] [DecidableEq I] [DecidableEq J]

theorem matrixTensorEquiv_symm_tmul (x : M → K) (y : N → K) :
    (matrixTensorEquiv K M N).symm (x ⊗ₜ[K] y) = Matrix.vecMulVec x y := by
  ext i j
  change ((Pi.basisFun K M).tensorProduct (Pi.basisFun K N)).equivFun (x ⊗ₜ[K] y) (i,j) =
    x i * y j
  simp only [Basis.equivFun_apply, Basis.tensorProduct_repr_tmul_apply,
    Pi.basisFun_repr, smul_eq_mul, mul_comm]

theorem matrixTensorEquiv_matrix_mul
    (C : Matrix I M K) (D : Matrix J N K) (A : Matrix M N K) :
    TensorProduct.map C.toLin' D.toLin' (matrixTensorEquiv K M N A) =
      matrixTensorEquiv K I J (C * A * Dᵀ) := by
  obtain ⟨z, rfl⟩ := (matrixTensorEquiv K M N).symm.surjective A
  rw [LinearEquiv.apply_symm_apply]
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    apply (matrixTensorEquiv K I J).symm.injective
    rw [LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, matrixTensorEquiv_symm_tmul,
      matrixTensorEquiv_symm_tmul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.vecMul_transpose]
    rfl
  | add x y hx hy =>
    simp only [map_add, Matrix.mul_add, Matrix.add_mul, hx, hy]

theorem range_le_oppositeAnnihilator (A : Matrix M N K) :
    A.toLin'.range ≤ imageFromLeftKernel Aᵀ.toLin'.ker := by
  rintro _ ⟨x, rfl⟩
  unfold imageFromLeftKernel
  rw [← dualKernel_eq_map_transpose]
  apply (Submodule.mem_dualCoannihilator _).mpr
  intro f hf
  exact LinearMap.congr_fun (LinearMap.mem_ker.mp hf) x

private theorem left_mul_eq_of_agree_on_range {A : Matrix M N K}
    {C C' : Matrix I M K}
    (h : ∀ x ∈ A.toLin'.range, C.toLin' x = C'.toLin' x) : C * A = C' * A := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro x
  simp only [Matrix.toLin'_mul, LinearMap.comp_apply]
  exact h (A.toLin' x) ⟨x, rfl⟩

theorem double_crop_eq_of_agree_on_ranges {A : Matrix M N K}
    {C C' : Matrix I M K} {D D' : Matrix J N K}
    (hC : ∀ x ∈ A.toLin'.range, C.toLin' x = C'.toLin' x)
    (hD : ∀ x ∈ Aᵀ.toLin'.range, D.toLin' x = D'.toLin' x) :
    C * A * Dᵀ = C' * A * D'ᵀ := by
  rw [left_mul_eq_of_agree_on_range hC, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  apply Matrix.transpose_injective
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using
    left_mul_eq_of_agree_on_range hD

section Decoding

variable {V W X Y : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

private theorem tensor_congr_map_coordinates
    (e : V ≃ₗ[K] (I → K)) (f : W ≃ₗ[K] (J → K))
    (p : (M → K) →ₗ[K] V) (q : (N → K) →ₗ[K] W) (A : Matrix M N K) :
    (TensorProduct.congr e f)
        (TensorProduct.map p q (matrixTensorEquiv K M N A)) =
      matrixTensorEquiv K I J
        (LinearMap.toMatrix' (e.toLinearMap.comp p) * A *
          (LinearMap.toMatrix' (f.toLinearMap.comp q))ᵀ) := by
  change ((TensorProduct.map e.toLinearMap f.toLinearMap).comp (TensorProduct.map p q))
    (matrixTensorEquiv K M N A) = _
  rw [← TensorProduct.map_comp]
  simpa only [Matrix.toLin'_toMatrix'] using
    matrixTensorEquiv_matrix_mul (LinearMap.toMatrix' (e.toLinearMap.comp p))
      (LinearMap.toMatrix' (f.toLinearMap.comp q)) A

/-- On the exact opposite row and column ranges, a reconstructed crop
computes the same tensor as the literal linear projections. -/
theorem tensor_crop_decode_eq
    (e : V ≃ₗ[K] (I → K)) (f : W ≃ₗ[K] (J → K))
    (p : (M → K) →ₗ[K] V) (q : (N → K) →ₗ[K] W)
    (dL : (X → K) →ₗ[K] V) (dR : (Y → K) →ₗ[K] W)
    (C : Matrix X M K) (D : Matrix Y N K) (A : Matrix M N K)
    (hC : ∀ x ∈ A.toLin'.range, dL (C.toLin' x) = p x)
    (hD : ∀ x ∈ Aᵀ.toLin'.range, dR (D.toLin' x) = q x) :
    TensorProduct.map dL dR (matrixTensorEquiv K X Y (C * A * Dᵀ)) =
      TensorProduct.map p q (matrixTensorEquiv K M N A) := by
  let L := LinearMap.toMatrix' (e.toLinearMap.comp dL)
  let R := LinearMap.toMatrix' (f.toLinearMap.comp dR)
  let L' := LinearMap.toMatrix' (e.toLinearMap.comp p)
  let R' := LinearMap.toMatrix' (f.toLinearMap.comp q)
  have hL : ∀ x ∈ A.toLin'.range, (L * C).toLin' x = L'.toLin' x := by
    intro x hx
    simp only [L, L', Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      LinearEquiv.coe_coe, hC x hx]
  have hR : ∀ x ∈ Aᵀ.toLin'.range, (R * D).toLin' x = R'.toLin' x := by
    intro x hx
    simp only [R, R', Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply,
      LinearEquiv.coe_coe, hD x hx]
  apply (TensorProduct.congr e f).injective
  rw [tensor_congr_map_coordinates, tensor_congr_map_coordinates]
  change matrixTensorEquiv K I J (L * (C * A * Dᵀ) * Rᵀ) =
    matrixTensorEquiv K I J (L' * A * R'ᵀ)
  congr 1
  rw [← double_crop_eq_of_agree_on_ranges hL hR, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

end Decoding

end
end Mathproof.EvenOrdinaryTISingular

#print axioms Mathproof.EvenOrdinaryTISingular.matrixTensorEquiv_matrix_mul
#print axioms Mathproof.EvenOrdinaryTISingular.double_crop_eq_of_agree_on_ranges
#print axioms Mathproof.EvenOrdinaryTISingular.tensor_crop_decode_eq
