import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PeirceDeterminants

open scoped BigOperators

theorem matrixUnits_intertwine {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [Ring R] (E F : ι → ι → R) (c a b : ι)
    (hE : ∀ i j k l, E i j * E k l = if j = k then E i l else 0)
    (hF : ∀ i j k l, F i j * F k l = if j = k then F i l else 0) :
    F a b * (∑ i, F i c * E c i) = (∑ i, F i c * E c i) * E a b := by
  classical
  simp only [Finset.mul_sum, Finset.sum_mul]
  have left : ∀ i, F a b * (F i c * E c i) =
      if i = b then F a c * E c b else 0 := by
    intro i
    rw [← mul_assoc, hF]
    by_cases h : i = b
    · subst i
      simp
    · simp [h, Ne.symm h]
  have right : ∀ i, (F i c * E c i) * E a b =
      if i = a then F a c * E c b else 0 := by
    intro i
    rw [mul_assoc, hE]
    by_cases h : i = a
    · subst i
      simp
    · simp [h]
  simp only [left, right, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem determinant_of_repeated_blocks {R ι κ : Type*} [CommRing R]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι R) :
    (Matrix.blockDiagonal (fun _ : κ => A)).det = A.det ^ Fintype.card κ := by
  rw [Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ]

theorem determinant_block_disappears {K ι κ : Type*} [Field K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι K) {g h m : ℕ} (hm : g * h = m)
    (hrep : g ∣ Fintype.card κ) (hexp : A.det ^ m = 1) :
    (Matrix.blockDiagonal (fun _ : κ => A)).det ^ h = 1 := by
  obtain ⟨v, hv⟩ := hrep
  rw [determinant_of_repeated_blocks, ← pow_mul, hv]
  have hmul : g * v * h = m * v := by
    rw [← hm]
    ac_rfl
  rw [hmul, pow_mul, hexp, one_pow]

end PeirceDeterminants
