import Mathlib.LinearAlgebra.Matrix.CharP
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

open Matrix Polynomial

/-- A square matrix of prime-power order in the defining characteristic
is killed by any prime power at least its side length. -/
theorem matrixPrimePowerOrderBound
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p s r : ℕ) [Fact p.Prime] [CharP K p] (M : Matrix ι ι K)
    (horder : M ^ (p ^ s) = 1) (hsize : Fintype.card ι ≤ p ^ r) :
    M ^ (p ^ r) = 1 := by
  have hcomm : Commute (M - 1) (1 : Matrix ι ι K) := Commute.one_right _
  have hpow (t : ℕ) : M ^ (p ^ t) = (M - 1) ^ (p ^ t) + 1 := by
    simpa [sub_add_cancel] using add_pow_char_pow_of_commute p t hcomm
  have hnil : IsNilpotent (M - 1) := by
    refine ⟨p ^ s, ?_⟩
    have h := (hpow s).symm.trans horder
    simpa using add_right_cancel (h.trans (zero_add (1 : Matrix ι ι K)).symm)
  have hchar : (M - 1).charpoly = X ^ Fintype.card ι :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hnil).eq_zero
  have hcard : (M - 1) ^ Fintype.card ι = 0 := by
    have hcay := Matrix.aeval_self_charpoly (M - 1)
    rw [hchar, map_pow, aeval_X] at hcay
    exact hcay
  rw [hpow, ← Nat.add_sub_of_le hsize, pow_add, hcard, zero_mul, zero_add]

/-- Transpose negation forces singularity in odd size and characteristic zero. -/
theorem oddSkewMatrixDetZero
    {K ι : Type*} [Field K] [CharZero K] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι K) (hodd : Odd (Fintype.card ι))
    (hskew : M.transpose = -M) : M.det = 0 := by
  have hd : M.det = -M.det := by
    calc
      M.det = M.transpose.det := (Matrix.det_transpose M).symm
      _ = (-M).det := congrArg Matrix.det hskew
      _ = -M.det := by rw [Matrix.det_neg, hodd.neg_pow, one_pow, neg_one_mul]
  exact add_self_eq_zero.mp (eq_neg_iff_add_eq_zero.mp hd)
