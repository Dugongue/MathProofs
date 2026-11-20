import EvenP6CellsCoded
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! A coefficient Gram matrix converts the contragredient of any simple
field multiplication into ordinary multiplication by the inverse word. -/

namespace EvenTI.LiveAlgebra

open scoped BigOperators Matrix
open Matrix EvenTI.CellProducer

variable {K D : Type} [Field K] [Fintype D] [DecidableEq D]

def wordMulMatrix (T : WordTable K D) (a : D → K) : Matrix D D K :=
  fun i j => T.multiply a (Pi.single j 1) i

private def wordMulLin (T : WordTable K D) [h : WordTable.Laws T] (a : D → K) :
    (D → K) →ₗ[K] (D → K) where
  toFun := T.multiply a
  map_add' x y := by
    rw [h.comm a (x+y), h.add_mul, h.comm x a, h.comm y a]
  map_smul' r x := by
    change T.multiply a (r • x) = r • T.multiply a x
    rw [h.comm a (r • x), h.smul_mul, h.comm x a]

theorem wordMulMatrix_mulVec (T : WordTable K D) [WordTable.Laws T] (a x : D → K) :
    (wordMulMatrix T a).mulVec x = T.multiply a x := by
  let L := wordMulLin T a
  have he : (∑ i, x i • Pi.single i (1 : K)) = x := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply, mul_ite, eq_comm]
  have h := congrArg L he
  rw [map_sum] at h
  ext i
  change (∑ j, T.multiply a (Pi.single j 1) i * x j) = T.multiply a x i
  rw [← show (∑ j, L (x j • Pi.single j (1 : K))) i = T.multiply a x i from congrFun h i,
    Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem wordMulMatrix_one (T : WordTable K D) [h : WordTable.Laws T] :
    wordMulMatrix T T.one = 1 := by
  ext i j
  change T.multiply T.one (Pi.single j 1) i = _
  rw [h.one_mul]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

theorem wordMulMatrix_mul (T : WordTable K D) [h : WordTable.Laws T] (a b : D → K) :
    wordMulMatrix T (T.multiply a b) = wordMulMatrix T a * wordMulMatrix T b := by
  ext i j
  change T.multiply (T.multiply a b) (Pi.single j 1) i =
    ((wordMulMatrix T a).mulVec (T.multiply b (Pi.single j 1))) i
  rw [wordMulMatrix_mulVec, h.assoc]

/-- The Gram pairing is the chosen output coefficient of multiplication. -/
def wordGram (T : WordTable K D) (k : D) : Matrix D D K :=
  fun i j => T.multiply (Pi.single i 1) (Pi.single j 1) k

theorem wordGram_mulVec (T : WordTable K D) [WordTable.Laws T] (k i : D)
    (x : D → K) :
    ((wordGram T k).mulVec x) i = T.multiply (Pi.single i 1) x k :=
  congrFun (wordMulMatrix_mulVec T (Pi.single i 1) x) k

/-- Obtain nonsingularity directly from the nonzero coordinate functional
and the verified field model, in every characteristic. -/
theorem wordGram_isUnit (T : WordTable K D) [h : WordTable.Laws T]
    {F : Type} [Field F] [Algebra K F] (E : (D → K) ≃ₗ[K] F)
    (hE : ∀ a b, E (T.multiply a b) = E a * E b) (k : D) :
    IsUnit (wordGram T k) := by
  apply Matrix.mulVec_injective_iff_isUnit.mp
  intro x y he
  have hz : (wordGram T k).mulVec (x-y) = 0 := by rw [Matrix.mulVec_sub, he, sub_self]
  by_contra hxy
  have hne : E (x-y) ≠ 0 := fun hzero =>
    sub_ne_zero.mpr hxy (E.injective (hzero.trans (E.map_zero.symm)))
  let a := E.symm (E (Pi.single k 1) / E (x-y))
  have hmul : T.multiply a (x-y) = Pi.single k 1 := by
    apply E.injective
    rw [hE, show E a = E (Pi.single k 1) / E (x-y) from E.apply_symm_apply _,
      div_mul_cancel₀ _ hne]
  have hzero (i : D) : T.multiply (Pi.single i 1) (x-y) k = 0 := by
    rw [← wordGram_mulVec T k i (x-y), hz]
    rfl
  have hh : T.multiply a (x-y) k = 0 := by
    rw [h.comm, ← wordMulMatrix_mulVec]
    simp only [Matrix.mulVec, dotProduct, wordMulMatrix, h.comm (x-y), hzero,
      zero_mul, Finset.sum_const_zero]
  have hbad : (1 : K) = 0 := by simpa [hmul] using hh
  exact one_ne_zero hbad

theorem wordGram_intertwines (T : WordTable K D) [h : WordTable.Laws T] (k : D)
    (a : D → K) :
    (wordMulMatrix T a)ᵀ * wordGram T k = wordGram T k * wordMulMatrix T a := by
  ext i j
  have hL : ((wordMulMatrix T a)ᵀ * wordGram T k) i j =
      T.multiply (Pi.single j 1) (T.multiply a (Pi.single i 1)) k := by
    rw [← wordGram_mulVec T k j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct, wordGram,
      wordMulMatrix]
    apply Finset.sum_congr rfl
    intro l _
    rw [h.comm (Pi.single l 1) (Pi.single j 1), mul_comm]
  have hR : (wordGram T k * wordMulMatrix T a) i j =
      T.multiply (Pi.single i 1) (T.multiply a (Pi.single j 1)) k := by
    rw [← wordGram_mulVec T k i]
    rfl
  rw [hL, hR, ← h.assoc, ← h.assoc, h.comm (Pi.single j 1) a, h.comm (Pi.single i 1) a,
    h.assoc, h.assoc, h.comm (Pi.single i 1) (Pi.single j 1)]

/-- If a previously chosen chart represents the primal action, its
inverse-transpose chart with the coefficient Gram represents the dual. -/
theorem dualGauge_intertwines {U V M P J : Matrix D D K}
    (h : P * U = V * M) (hU : IsUnit U) (hV : IsUnit V) (hP : IsUnit P) (hM : IsUnit M)
    (hJ : Mᵀ * J = J * M) :
    (P⁻¹)ᵀ * ((U⁻¹)ᵀ * J) = (V⁻¹)ᵀ * J * M⁻¹ := by
  have hUd := (Matrix.isUnit_iff_isUnit_det U).mp hU
  have hVd := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hPd := (Matrix.isUnit_iff_isUnit_det P).mp hP
  have hMd := (Matrix.isUnit_iff_isUnit_det M).mp hM
  have e : P⁻¹ * V = U * M⁻¹ := by
    calc
      P⁻¹ * V = P⁻¹ * ((V * M) * M⁻¹) := by
        rw [Matrix.mul_assoc V, Matrix.mul_nonsing_inv _ hMd, Matrix.mul_one]
      _ = U * M⁻¹ := by
        rw [← h, ← Matrix.mul_assoc P⁻¹ (P * U), ← Matrix.mul_assoc P⁻¹ P U,
          Matrix.nonsing_inv_mul _ hPd, Matrix.one_mul]
  have eₜ : Vᵀ * (P⁻¹)ᵀ = (M⁻¹)ᵀ * Uᵀ := by
    simpa only [Matrix.transpose_mul] using congrArg Matrix.transpose e
  have hleft : (V⁻¹)ᵀ * Vᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hVd, Matrix.transpose_one]
  have hright : Uᵀ * (U⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hUd, Matrix.transpose_one]
  have hpush : (P⁻¹)ᵀ * (U⁻¹)ᵀ = (V⁻¹)ᵀ * (M⁻¹)ᵀ := by
    calc
      _ = ((V⁻¹)ᵀ * Vᵀ) * (P⁻¹)ᵀ * (U⁻¹)ᵀ := by rw [hleft, Matrix.one_mul]
      _ = (V⁻¹)ᵀ * ((M⁻¹)ᵀ * Uᵀ) * (U⁻¹)ᵀ := by
        rw [Matrix.mul_assoc (V⁻¹)ᵀ Vᵀ, eₜ]
      _ = _ := by rw [Matrix.mul_assoc (V⁻¹)ᵀ, Matrix.mul_assoc ((M⁻¹)ᵀ), hright, Matrix.mul_one]
  have hleftM : (M⁻¹)ᵀ * Mᵀ = 1 := by
    rw [← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hMd, Matrix.transpose_one]
  have hmove : (M⁻¹)ᵀ * J = J * M⁻¹ := by
    calc
      _ = (M⁻¹)ᵀ * (J * M) * M⁻¹ := by
        rw [Matrix.mul_assoc (M⁻¹)ᵀ, Matrix.mul_assoc J, Matrix.mul_nonsing_inv _ hMd, Matrix.mul_one]
      _ = (M⁻¹)ᵀ * (Mᵀ * J) * M⁻¹ := by rw [hJ]
      _ = _ := by rw [← Matrix.mul_assoc (M⁻¹)ᵀ Mᵀ, hleftM, Matrix.one_mul]
  rw [← Matrix.mul_assoc, hpush, Matrix.mul_assoc, hmove, ← Matrix.mul_assoc]

#print axioms wordMulMatrix_mulVec
#print axioms wordGram_isUnit
#print axioms wordGram_intertwines
#print axioms dualGauge_intertwines

end EvenTI.LiveAlgebra
