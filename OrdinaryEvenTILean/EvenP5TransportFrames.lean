import EvenP5TransportLift

namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped Matrix TensorProduct
open Matrix EvenTI.Action EvenTI.AnchorCovariance
noncomputable section

variable {K : Type*} [Field K] {a k b m n : ℕ}

local notation "Side" => (Fin a ⊕ Fin k)

private def transUnit {X : Type*} [Fintype X] [DecidableEq X] (U : (Matrix X X K)ˣ) :
    (Matrix X X K)ˣ where
  val := U.valᵀ
  inv := U.invᵀ
  val_inv := by rw [← Matrix.transpose_mul, U.inv_val, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, U.val_inv, Matrix.transpose_one]

private def reframe {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (u v : X ≃ Y) (G : (Matrix Y Y K)ˣ) : (Matrix X X K)ˣ where
  val := G.val.submatrix u v
  inv := G.inv.submatrix v u
  val_inv := by rw [Matrix.submatrix_mul_equiv, G.val_inv, Matrix.submatrix_one_equiv]
  inv_val := by rw [Matrix.submatrix_mul_equiv, G.inv_val, Matrix.submatrix_one_equiv]

private theorem asMatrix_act (g : Changes K 2 n) (x : Coord 2 n → K) :
    asMatrix n (act g x) = (g 0).val * asMatrix n x * (g 1).valᵀ := by
  let e := (Equiv.funUnique (Fin 1) (Fin n)).symm
  let f := Equiv.refl (Fin n)
  have h (y : Coord 2 n → K) : asMatrix n y = (retainedForm 0 y).submatrix f e := rfl
  rw [h, h, retainedForm_act]
  have hR : (productMatrix (fun j : Fin 1 => g ((0 : Fin 2).succAbove j))).submatrix e e =
      (g 1).val := by
    ext i j
    change (∏ t : Fin 1, (g ((0 : Fin 2).succAbove t)).val (e i t) (e j t)) = _
    simp [e]
  rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.transpose_submatrix, hR,
    ← Matrix.submatrix_mul_equiv _ _ _ f] <;> rfl

private theorem asMatrix_move (g : Changes K 2 n) (x : Coord 2 n → K) :
    asMatrix n (moveCutForm (productUnit g) x) = (g 0).invᵀ * asMatrix n x * (g 1).inv := by
  have h : moveCutForm (productUnit g) x = act (dualChanges g) x := by
    rw [act, dual_product]
    rfl
  rw [h, asMatrix_act]
  change (g 0).invᵀ * asMatrix n x * ((g 1).invᵀ)ᵀ = _
  rw [Matrix.transpose_transpose]

private theorem reframe_identity
    {ell : Coord 2 n → K} (g : Changes K 2 n)
    (P : NormalPair ell a k) (P' : NormalPair (moveCutForm (productUnit g) ell) a k) :
    ∃ A B : (Matrix Side Side K)ˣ,
      A.valᵀ * normalPair a k * B.val = normalPair a k ∧
      ∀ x, orient _ P' (act g x) = A.val * orient _ P x * B.valᵀ := by
  let G₁ := transUnit (P'.left⁻¹) * g 0 * transUnit P.left
  let G₂ := P'.right⁻¹ * g 1 * P.right
  let e := P.indices.symm
  let e' := P'.indices.symm
  let A := reframe e' e G₁
  let B := reframe e' e G₂
  have g₁ : G₁.val = P'.left.invᵀ * (g 0).val * P.left.valᵀ := rfl
  have g₂ : G₂.val = P'.right.inv * (g 1).val * P.right.val := rfl
  refine ⟨A, B, ?_, ?_⟩
  · conv_lhs => rw [← P'.normalized]
    conv_rhs => rw [← P.normalized]
    change (G₁.val.submatrix e' e)ᵀ *
        (P'.left.val * asMatrix n (moveCutForm (productUnit g) ell) * P'.right.val).submatrix e' e' *
        (G₂.val.submatrix e' e) = (P.left.val * asMatrix n ell * P.right.val).submatrix e e
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    congr 1
    rw [g₁, g₂, asMatrix_move]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
    have hcancel : (g 0).valᵀ * (g 0).invᵀ = 1 :=
      (transUnit (g 0)).val_inv
    calc
      _ = P.left.val * (g 0).valᵀ * (P'.left.inv * P'.left.val) *
          (g 0).invᵀ * asMatrix n ell * (g 1).inv *
          (P'.right.val * P'.right.inv) * (g 1).val * P.right.val := by
        simp only [Matrix.mul_assoc]
      _ = P.left.val * ((g 0).valᵀ * (g 0).invᵀ) * asMatrix n ell *
          ((g 1).inv * (g 1).val) * P.right.val := by
        simp only [Units.inv_val, Units.val_inv, Matrix.one_mul, Matrix.mul_one,
          Matrix.mul_assoc]
      _ = _ := by rw [hcancel, (g 1).inv_val, Matrix.mul_one, Matrix.mul_one]
  · intro x
    change
      (P'.left.invᵀ * asMatrix n (act g x) * P'.right.invᵀ).submatrix e' e' =
      (G₁.val.submatrix e' e) *
        ((P.left.invᵀ * asMatrix n x * P.right.invᵀ).submatrix e e) *
        (G₂.val.submatrix e' e)ᵀ
    rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    congr 1
    rw [g₁, g₂, Matrix.transpose_mul, Matrix.transpose_mul, asMatrix_act]
    have hL : P.left.valᵀ * P.left.invᵀ = 1 := (transUnit P.left).val_inv
    have hR : P.right.invᵀ * P.right.valᵀ = 1 := (transUnit P.right).inv_val
    symm
    calc
      _ = P'.left.invᵀ * (g 0).val * (P.left.valᵀ * P.left.invᵀ) *
          asMatrix n x * (P.right.invᵀ * P.right.valᵀ) * (g 1).valᵀ * P'.right.invᵀ := by
        simp only [Matrix.mul_assoc]
      _ = _ := by simp only [hL, hR, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]

private theorem enlargedProjection_move {ell : Coord 2 n → K} (g : Changes K 2 n)
    (P : NormalPair ell a k) (P' : NormalPair (moveCutForm (productUnit g) ell) a k) :
    ∃ U : (Matrix (Index a k) (Index a k) K)ˣ, ∀ x,
      enlargedProjection _ P' (act g x) = U.val * enlargedProjection _ P x * U.inv := by
  obtain ⟨A, B, h, hAct⟩ := reframe_identity g P P'
  obtain ⟨U, hU⟩ := enlargedPair_transport A B h
  refine ⟨U, fun x => ?_⟩
  change enlargedPair a k (orient _ P' (act g x)) =
    U.val * enlargedPair a k (orient _ P x) * U.inv
  rw [hAct]
  exact hU _

/-- Any source and target normal frames produce conjugate literal enlarged
operators when the target forms are the contragredient images. -/
theorem rawEnlarged_transport
    {ell rho : Coord 2 n → K}
    (g : Changes K (2 + 2) n) (X : Tensor K (2 + 2) n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm g ell) a k) (R' : NormalPair (moveRightForm g rho) b m) :
    ∃ U : (Matrix (Index a k) (Index a k) K)ˣ,
      ∃ V : (Matrix (Index b m) (Index b m) K)ˣ,
        rawEnlarged L' R' (act g X) =
          kronecker U.val V.val * rawEnlarged L R X * kronecker U.inv V.inv := by
  obtain ⟨U, hU⟩ := enlargedProjection_move (leftModes g) L L'
  obtain ⟨V, hV⟩ := enlargedProjection_move (rightModes g) R R'
  refine ⟨U, V, ?_⟩
  unfold rawEnlarged
  rw [flatten_action, ← matrixTensorEquiv_matrix_mul]
  let Z := matrixTensorEquiv K _ _ (flatten (l := 2) (r := 2) X)
  change enlargedMatrix L' R' (TensorProduct.map _ _ Z) =
    kronecker U.val V.val * enlargedMatrix L R Z * kronecker U.inv V.inv
  induction Z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Matrix.mul_add, Matrix.add_mul, hx, hy]
  | tmul x y =>
    simp only [enlargedMatrix, LinearMap.comp_apply, LinearEquiv.coe_coe,
      TensorProduct.map_tmul, kroneckerLinearEquiv_tmul]
    change Matrix.kronecker (enlargedProjection _ L' (act (leftModes g) x))
        (enlargedProjection _ R' (act (rightModes g) y)) =
      kronecker U.val V.val * kronecker (enlargedProjection _ L x) (enlargedProjection _ R y) *
        kronecker U.inv V.inv
    have hU' : enlargedProjection (moveLeftForm g ell) L' (act (leftModes g) x) =
        U.val * enlargedProjection _ L x * U.inv := hU x
    have hV' : enlargedProjection (moveRightForm g rho) R' (act (rightModes g) y) =
        V.val * enlargedProjection _ R y * V.inv := hV y
    rw [hU', hV']
    unfold Matrix.kronecker
    rw [Matrix.mul_kronecker_mul, Matrix.mul_kronecker_mul]

/-- The order-four actual enlarged characteristic polynomial tests survive
all genuine transporters and all choices of target normal bases. -/
theorem rawEnlarged_charpolys_transport
    {ell rho : Coord 2 n → K}
    (g : Changes K (2 + 2) n) (X : Tensor K (2 + 2) n)
    (L : NormalPair ell a k) (R : NormalPair rho b m)
    (L' : NormalPair (moveLeftForm g ell) a k) (R' : NormalPair (moveRightForm g rho) b m) :
    (partialTraceLeft (rawEnlarged L' R' (act g X) ^ 2)).charpoly =
        (partialTraceLeft (rawEnlarged L R X ^ 2)).charpoly ∧
      (partialTraceRight (rawEnlarged L' R' (act g X) ^ 2)).charpoly =
        (partialTraceRight (rawEnlarged L R X ^ 2)).charpoly := by
  obtain ⟨U, V, h⟩ := rawEnlarged_transport g X L R L' R'
  rw [h]
  exact quadratic_charpoly _ U.val U.inv V.val V.inv U.inv_val V.inv_val

private theorem moveForm_one (x : Coord 2 n → K) :
    moveCutForm (productUnit (1 : Changes K 2 n)) x = x := by
  change (productMatrix ((1 : Changes K 2 n)⁻¹))ᵀ.mulVec x = x
  rw [inv_one, productMatrix_one, Matrix.transpose_one, Matrix.one_mulVec]

private theorem rawEnlarged_relabel_forms
    {ell ell' rho rho' : Coord 2 n → K} (hL : ell = ell') (hR : rho = rho')
    (L : NormalPair ell a k) (R : NormalPair rho b m) (X : Tensor K 4 n) :
    rawEnlarged (hL ▸ L) (hR ▸ R) X = rawEnlarged L R X := by
  cases hL
  cases hR
  rfl

/-- The squared partial-trace characteristic polynomials do not depend on
the chosen normal frames for either raw form. -/
theorem rawEnlarged_charpolys_frame_choice
    {ell rho : Coord 2 n → K} (X : Tensor K 4 n)
    (L₁ L₂ : NormalPair ell a k) (R₁ R₂ : NormalPair rho b m) :
    (partialTraceLeft (rawEnlarged L₂ R₂ X ^ 2)).charpoly =
        (partialTraceLeft (rawEnlarged L₁ R₁ X ^ 2)).charpoly ∧
      (partialTraceRight (rawEnlarged L₂ R₂ X ^ 2)).charpoly =
        (partialTraceRight (rawEnlarged L₁ R₁ X ^ 2)).charpoly := by
  have hl : leftModes (l := 2) (r := 2) (1 : Changes K 4 n) = 1 := rfl
  have hr : rightModes (l := 2) (r := 2) (1 : Changes K 4 n) = 1 := rfl
  have hL : moveLeftForm (l := 2) (r := 2) (1 : Changes K 4 n) ell = ell := by
    rw [moveLeftForm, hl]
    exact moveForm_one ell
  have hR : moveRightForm (l := 2) (r := 2) (1 : Changes K 4 n) rho = rho := by
    rw [moveRightForm, hr]
    exact moveForm_one rho
  let P : NormalPair (moveLeftForm (l := 2) (r := 2) (1 : Changes K 4 n) ell) a k := hL.symm ▸ L₂
  let Q : NormalPair (moveRightForm (l := 2) (r := 2) (1 : Changes K 4 n) rho) b m := hR.symm ▸ R₂
  have h := rawEnlarged_charpolys_transport 1 X L₁ R₁ P Q
  dsimp only [P, Q] at h
  rw [act_one, rawEnlarged_relabel_forms hL.symm hR.symm] at h
  exact h

end
end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.rawEnlarged_transport
#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.rawEnlarged_charpolys_transport
#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.rawEnlarged_charpolys_frame_choice
