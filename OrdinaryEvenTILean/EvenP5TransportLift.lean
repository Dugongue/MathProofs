import EvenP3SingularActual

namespace Mathproof.EvenOrdinaryTISingular.EnlargedCut

open scoped Matrix
open Matrix
noncomputable section

variable {K : Type*} [Field K] {a k : ℕ}

local notation "Side" => (Fin a ⊕ Fin k)

private def primalEmbedding : Side ↪ Index a k where
  toFun
    | .inl i => .inr (.inl i)
    | .inr j => .inl j
  inj' := by
    intro x y h
    cases x <;> cases y <;> simp_all

private def dualEmbedding : Side ↪ Index a k := ⟨Sum.inr, Sum.inr_injective⟩

@[simp] private theorem primal_inl (i : Fin a) :
    primalEmbedding (Sum.inl i : Side) = Sum.inr (Sum.inl i) := rfl

@[simp] private theorem primal_inr (i : Fin k) :
    primalEmbedding (Sum.inr i : Side) = Sum.inl i := rfl

private def embedMat {X Y : Type*} [DecidableEq Y] (e : X ↪ Y) : Matrix Y X K :=
  fun i j => if i = e j then 1 else 0

local notation "U₀" => (embedMat (K := K) (primalEmbedding (a := a) (k := k)))
local notation "V₀" => (embedMat (K := K) (dualEmbedding (a := a) (k := k)))

private theorem enlargedPair_coordinates (X : Matrix Side Side K) :
    enlargedPair a k X = U₀ * X * V₀ᵀ := by
  ext i j
  rw [Matrix.mul_assoc]
  rcases i with i | (i | i) <;> rcases j with j | (j | j) <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, embedMat, dualEmbedding,
      Fintype.sum_sum_type, ite_mul, mul_ite, eq_comm] <;>
    rfl

private def liftMat (A W : Matrix Side Side K) : Matrix (Index a k) (Index a k) K :=
  Matrix.fromBlocks A.toBlocks₂₂
    (Matrix.of (fun i j => match j with | .inl j => A.toBlocks₂₁ i j | .inr _ => 0))
    0
    (Matrix.fromBlocks A.toBlocks₁₁ (W.toBlocks₂₁)ᵀ 0 (W.toBlocks₂₂)ᵀ)

private theorem pairing_blocks (A B : (Matrix Side Side K)ˣ)
    (h : A.valᵀ * normalPair a k * B.val = normalPair a k) :
    A.val.toBlocks₁₂ = 0 ∧ B.inv.toBlocks₁₂ = 0 ∧ A.val.toBlocks₁₁ᵀ = B.inv.toBlocks₁₁ := by
  have hEq : A.valᵀ * normalPair a k = normalPair a k * B.inv := by
    calc
      _ = A.valᵀ * normalPair a k * (B.val * B.inv) := by rw [B.val_inv, Matrix.mul_one]
      _ = (A.valᵀ * normalPair a k * B.val) * B.inv := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h]
  have hl : A.valᵀ * normalPair a k =
      Matrix.fromBlocks A.val.toBlocks₁₁ᵀ 0 A.val.toBlocks₁₂ᵀ 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks A.val]
    simp [normalPair, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  have hr : normalPair a k * B.inv =
      Matrix.fromBlocks B.inv.toBlocks₁₁ B.inv.toBlocks₁₂ 0 0 := by
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks B.inv]
    simp [normalPair, Matrix.fromBlocks_multiply]
  rw [hl, hr, Matrix.fromBlocks_inj] at hEq
  exact ⟨Matrix.transpose_injective (hEq.2.2.1.trans Matrix.transpose_zero.symm),
    hEq.2.1.symm, hEq.1⟩

private theorem liftMat_primal (A W : Matrix Side Side K) (h : A.toBlocks₁₂ = 0) :
    liftMat A W * U₀ = U₀ * A := by
  have hz (i : Fin a) (j : Fin k) : A (.inl i) (.inr j) = 0 := congrFun₂ h i j
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, embedMat, Fintype.sum_sum_type, mul_ite, ite_mul,
      liftMat, Matrix.toBlocks₁₁, Matrix.toBlocks₂₁, Matrix.toBlocks₂₂,
      Matrix.submatrix_apply, hz, eq_comm]

private theorem liftMat_dual (A W : Matrix Side Side K) (h₁ : W.toBlocks₁₂ = 0)
    (h₂ : A.toBlocks₁₁ᵀ = W.toBlocks₁₁) :
    (liftMat A W)ᵀ * V₀ = V₀ * W := by
  have hz (i : Fin a) (j : Fin k) : W (.inl i) (.inr j) = 0 := congrFun₂ h₁ i j
  have hW (i j : Fin a) : A (.inl j) (.inl i) = W (.inl i) (.inl j) := congrFun₂ h₂ i j
  ext i j
  rcases i with i | (i | i) <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, embedMat, dualEmbedding,
      Fintype.sum_sum_type, mul_ite, ite_mul, liftMat, Matrix.fromBlocks, Matrix.toBlocks₁₁,
      Matrix.toBlocks₂₁, Matrix.toBlocks₂₂, Matrix.submatrix_apply, hz, hW, eq_comm]

private theorem nonzero_diag_of_lower (M : Matrix Side Side K)
    (h : M.toBlocks₁₂ = 0) (hM : IsUnit M) :
    M.toBlocks₁₁.det ≠ 0 ∧ M.toBlocks₂₂.det ≠ 0 := by
  have hdet : M.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).mp hM).ne_zero
  have hBlock : M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
    rw [← Matrix.det_fromBlocks_zero₁₂ M.toBlocks₁₁ M.toBlocks₂₁ M.toBlocks₂₂,
      ← h, Matrix.fromBlocks_toBlocks]
  rw [hBlock, mul_ne_zero_iff] at hdet
  exact hdet

private theorem liftMat_isUnit (A W : Matrix Side Side K) (hA : IsUnit A) (hW : IsUnit W)
    (ha : A.toBlocks₁₂ = 0) (hw : W.toBlocks₁₂ = 0) : IsUnit (liftMat A W) := by
  obtain ⟨h11, h22⟩ := nonzero_diag_of_lower A ha hA
  obtain ⟨_, w22⟩ := nonzero_diag_of_lower W hw hW
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  rw [liftMat, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁, Matrix.det_transpose]
  exact mul_ne_zero h22 (mul_ne_zero h11 w22)

/-- Every isometry of a normal singular pairing extends to a change of basis
on its perfect enlargement.  The same change works for all coefficients. -/
theorem enlargedPair_transport (A B : (Matrix Side Side K)ˣ)
    (h : A.valᵀ * normalPair a k * B.val = normalPair a k) :
    ∃ P : (Matrix (Index a k) (Index a k) K)ˣ, ∀ X : Matrix Side Side K,
      enlargedPair a k (A.val * X * B.valᵀ) = P.val * enlargedPair a k X * P.inv := by
  obtain ⟨ha, hb, hc⟩ := pairing_blocks A B h
  obtain ⟨P, hP⟩ := liftMat_isUnit A.val B.inv A.isUnit (B⁻¹).isUnit ha hb
  have hu : P.val * U₀ = U₀ * A.val := by
    rw [hP]
    exact liftMat_primal A.val B.inv ha
  have hv : P.valᵀ * V₀ = V₀ * B.inv := by
    rw [hP]
    exact liftMat_dual A.val B.inv hb hc
  have hv' : B.valᵀ * V₀ᵀ = V₀ᵀ * P.inv := by
    have hi : B.valᵀ * B.invᵀ = 1 := by rw [← Matrix.transpose_mul, B.inv_val, Matrix.transpose_one]
    have ht := congrArg Matrix.transpose hv
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose] at ht
    calc
      _ = (B.valᵀ * V₀ᵀ) * (P.val * P.inv) := by
        rw [P.val_inv, Matrix.mul_one]
      _ = B.valᵀ * (V₀ᵀ * P.val) * P.inv := by
        simp only [Matrix.mul_assoc]
      _ = (B.valᵀ * B.invᵀ) * V₀ᵀ * P.inv := by
        rw [ht, Matrix.mul_assoc B.valᵀ B.invᵀ]
      _ = _ := by rw [hi, Matrix.one_mul]
  refine ⟨P, fun X => ?_⟩
  rw [enlargedPair_coordinates, enlargedPair_coordinates]
  rw [show U₀ * (A.val * X * B.valᵀ) * V₀ᵀ =
    (U₀ * A.val) * X * (B.valᵀ * V₀ᵀ) by
      simp only [Matrix.mul_assoc]]
  rw [← hu, hv']
  simp only [Matrix.mul_assoc]

end
end Mathproof.EvenOrdinaryTISingular.EnlargedCut

#print axioms Mathproof.EvenOrdinaryTISingular.EnlargedCut.enlargedPair_transport
