import EvenFlattening
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.FieldTheory.Finite.Basic

namespace EvenTI.Action

open Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {n l : Nat}

private theorem nonscalar_offDiagonal (p : (Matrix (Fin n) (Fin n) K)ˣ) (hn : 0 < n)
    (hp : ¬ ∃ u : Kˣ, p = scalar u) :
    ∃ h : (Matrix (Fin n) (Fin n) K)ˣ,
      ∃ x y : Fin n, x ≠ y ∧ (h * p * h⁻¹).val x y ≠ 0 := by
  by_cases ho : ∃ x y : Fin n, x ≠ y ∧ p.val x y ≠ 0
  · refine ⟨1, ?_⟩
    simpa using ho
  push_neg at ho
  have hdiag : ∃ x y : Fin n, p.val x x ≠ p.val y y := by
    by_contra same
    push_neg at same
    let i : Fin n := ⟨0, hn⟩
    let c := p.val i i
    have hc : p.val = c • (1 : Matrix (Fin n) (Fin n) K) := by
      ext x y
      by_cases hxy : x = y
      · subst y
        simpa [c] using same x i
      · simp [Matrix.one_apply, hxy, ho x y hxy]
    have hnonzero : c ≠ 0 := by
      letI : Nonempty (Fin n) := ⟨i⟩
      intro h
      have hp0 : p.val = 0 := by simpa [h] using hc
      exact p.isUnit.ne_zero hp0
    apply hp
    refine ⟨Units.mk0 c hnonzero, ?_⟩
    apply Units.ext
    simpa [scalar_val] using hc
  obtain ⟨x, y, hxy⟩ := hdiag
  have hne : x ≠ y := fun h => hxy (congrArg (fun i => p.val i i) h)
  let E : Matrix (Fin n) (Fin n) K := Matrix.single x y 1
  have hE : E * E = 0 := by
    change Matrix.single x y (1 : K) * Matrix.single x y 1 = 0
    exact Matrix.single_mul_single_of_ne (1 : K) x y x (Ne.symm hne) 1
  let h : (Matrix (Fin n) (Fin n) K)ˣ :=
    ⟨1 + E, 1 - E, by simp [add_mul, mul_sub, hE], by simp [sub_mul, mul_add, hE]⟩
  refine ⟨h, x, y, hne, ?_⟩
  change (((1 + E) * p.val) * (1 - E)) x y ≠ 0
  have hval : (((1 + E) * p.val) * (1 - E)) x y = p.val y y - p.val x x := by
    simp [E, add_mul, mul_sub, ho x y hne, ho y x (Ne.symm hne)]
  rw [hval]
  exact sub_ne_zero.mpr (Ne.symm hxy)

theorem rank_sub_one_of_offDiagonal (g : Changes K (l + 1) n)
    (i : Fin (l + 1)) (x y : Fin n) (hne : x ≠ y) (hx : (g i).val x y ≠ 0) :
    n ^ l ≤ (productMatrix g - 1).rank := by
  let rows := fun u : Coord l n => retainedMode i (x, u)
  let cols := fun v : Coord l n => retainedMode i (y, v)
  have hblock : (productMatrix g - 1).submatrix rows cols =
      (g i).val x y • productMatrix (fun j => g (i.succAbove j)) := by
    ext u v
    have huv : rows u ≠ cols v := by
      intro h
      exact hne (congrArg Prod.fst ((retainedMode i).injective h))
    simp [rows, cols, Matrix.one_apply, huv, retained_productMatrix]
  calc
    n ^ l = (productMatrix (fun j => g (i.succAbove j))).rank := by
      rw [← cut_side_card n l]
      exact (Matrix.rank_unit (productUnit (fun j => g (i.succAbove j)))).symm
    _ = ((productMatrix g - 1).submatrix rows cols).rank := by
      rw [hblock, rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hx)]
    _ ≤ _ := Matrix.rank_submatrix_le _ _ _

theorem rank_sub_one_of_nonscalar (g : Changes K (l + 1) n) (i : Fin (l + 1))
    (hn : 0 < n) (hp : ¬ ∃ u : Kˣ, g i = scalar u) :
    n ^ l ≤ (productMatrix g - 1).rank := by
  obtain ⟨h, x, y, hxy, hoff⟩ := nonscalar_offDiagonal (g i) hn hp
  let a : Changes K (l + 1) n := fun _ => h
  have h1 : productMatrix a * (productMatrix g - 1) * productMatrix a⁻¹ =
      productMatrix (a * g * a⁻¹) - 1 := by
    simp only [mul_sub, sub_mul, Matrix.mul_one, ← productMatrix_mul, mul_inv_cancel, productMatrix_one]
  calc
    _ ≤ (productMatrix (a * g * a⁻¹) - 1).rank :=
      rank_sub_one_of_offDiagonal (a * g * a⁻¹) i x y hxy hoff
    _ ≤ _ := by
      rw [← h1]
      exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

#print axioms rank_sub_one_of_offDiagonal
#print axioms rank_sub_one_of_nonscalar

end EvenTI.Action
