/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).

Adapted from the algebraic Berkowitz modules in edemaine/lean-canny at
af8d9dc4284a3e8724ef71bfc1de506baea23f08. This port collects the Mathlib-only
dependency closure in one module and adapts its names and compatibility proofs.
-/

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.BigOperators.Group.List.Basic

noncomputable section

-- Ported from LeanCanny/Algebra/BorderedDeterminant.lean
/-!
# Bordered determinants without inversion

A block elimination matrix proves the adjugate formula for a bordered
determinant when the smaller determinant is regular. In particular, the
determinant of a characteristic matrix is monic and can be cancelled over
any commutative coefficient ring, including rings with zero divisors.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz
open Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def border (a : R) (r c : ι → R) (D : Matrix ι ι R) : Matrix (Unit ⊕ ι) (Unit ⊕ ι) R :=
  fromBlocks (a • (1 : Matrix Unit Unit R)) (replicateRow Unit r) (replicateCol Unit c) D

theorem det_border_of_isRegular (a : R) (r c : ι → R) (D : Matrix ι ι R)
    (hD : IsRegular D.det) :
    (border a r c D).det = a * D.det - r ⬝ᵥ (D.adjugate *ᵥ c) := by
  let B := replicateRow Unit r
  let C := replicateCol Unit c
  let P := fromBlocks (D.det • (1 : Matrix Unit Unit R)) (-(B * D.adjugate))
    (0 : Matrix ι Unit R) (1 : Matrix ι ι R)
  have hprod : P * border a r c D =
      fromBlocks (D.det • (a • (1 : Matrix Unit Unit R)) - B * D.adjugate * C) 0 C D := by
    dsimp only [P, border]
    rw [fromBlocks_multiply]
    congr 1
    · simp [B, C, Matrix.neg_mul, sub_eq_add_neg, smul_smul, mul_comm]
    · simp [B, Matrix.smul_mul, Matrix.neg_mul, Matrix.mul_assoc, adjugate_mul, Matrix.mul_smul]
    · simp [C]
    · simp
  have hdet := congrArg Matrix.det hprod
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂] at hdet
  apply hD.left
  simp [B, C, det_unique, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Finset.mul_sum, mul_comm, mul_left_comm] at hdet
  rw [Finset.sum_comm] at hdet
  simpa [dotProduct, mulVec, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm] using hdet

end Mathproof.MinimumGeneration.RankBerkowitz

-- Ported from LeanCanny/Algebra/CharacteristicAdjugate.lean
/-!
# Characteristic adjugates through matrix powers

The adjugate of `X I - A` is the quotient of the scalar characteristic
polynomial by `X - A`, in the polynomial ring with matrix coefficients.
Synthetic division therefore expresses every coefficient using powers of A.
These division-free coefficient identities are ingredients of the bordered
characteristic-polynomial recurrence used by Berkowitz's algorithm.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem adjugate_charmatrix_eq_div (A : Matrix ι ι R) :
    matPolyEquiv (adjugate (charmatrix A)) =
      A.charpoly.map (algebraMap R (Matrix ι ι R)) /ₘ (X - C A) := by
  have h := congrArg matPolyEquiv (mul_adjugate (charmatrix A))
  rw [map_mul, matPolyEquiv_charmatrix, matPolyEquiv_smul_one] at h
  change (X - C A) * matPolyEquiv (adjugate (charmatrix A)) =
    A.charpoly.map (algebraMap R (Matrix ι ι R)) at h
  rw [← h, mul_divByMonic_cancel_left _ (monic_X_sub_C A)]

theorem adjugate_charmatrix_coeff_matrix (A : Matrix ι ι R) (d : ℕ) :
    (matPolyEquiv (adjugate (charmatrix A))).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A ^ (k - (d + 1)) * algebraMap R (Matrix ι ι R) (A.charpoly.coeff k) := by
  nontriviality R
  rw [adjugate_charmatrix_eq_div, coeff_divByMonic_X_sub_C]
  simp only [coeff_map]
  let p := A.charpoly.map (algebraMap R (Matrix ι ι R))
  have hp : p.natDegree ≤ Fintype.card ι :=
    natDegree_map_le.trans_eq (charpoly_natDegree_eq_dim A)
  apply sum_subset (by intro k hk; exact mem_Icc.mpr ⟨(mem_Icc.mp hk).1, (mem_Icc.mp hk).2.trans hp⟩)
  · intro k hk hkn
    have hkd : (A.charpoly.map (algebraMap R (Matrix ι ι R))).natDegree < k := by
      have := mem_Icc.mp hk
      simp only [mem_Icc, not_and_or, not_le] at hkn
      omega
    rw [← coeff_map, coeff_eq_zero_of_natDegree_lt hkd, mul_zero]

theorem adjugate_charmatrix_coeff (A : Matrix ι ι R) (d : ℕ) (i j : ι) :
    (adjugate (charmatrix A) i j).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A.charpoly.coeff k * (A ^ (k - (d + 1))) i j := by
  have h := congrArg (fun M : Matrix ι ι R => M i j) (adjugate_charmatrix_coeff_matrix A d)
  simpa [matPolyEquiv_coeff_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.algebraMap_matrix_apply,
    Matrix.diagonal, mul_comm] using h

end Mathproof.MinimumGeneration.RankBerkowitz

-- Ported from LeanCanny/Algebra/BerkowitzRecurrence.lean
/-!
# The division-free bordered characteristic-polynomial recurrence

For a matrix bordered by scalar `a`, row `r`, and column `c`, the new
characteristic polynomial is `(X-a) χ_A - r adj(XI-A) c`. Every coefficient
of the correction is a convolution of characteristic coefficients with
the scalar moments `r A^k c`. These identities hold over any commutative
ring. `BerkowitzProduct` and `BerkowitzBalanced` give the product formulation
and balanced entry recursion. Encoded evaluation and workspace certification
of the resulting determinant algorithm remain separate obligations.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

def borderMoment (r c : ι → R) (A : Matrix ι ι R) (k : ℕ) : R := r ⬝ᵥ (A ^ k *ᵥ c)

theorem charmatrix_border (a : R) (r c : ι → R) (A : Matrix ι ι R) :
    charmatrix (border a r c A) =
      border (X - C a) (fun i => -C (r i)) (fun i => -C (c i)) (charmatrix A) := by
  ext (⟨⟩ | i) (⟨⟩ | j) <;>
    simp [border, charmatrix, Matrix.diagonal, sub_eq_add_neg]

theorem charpoly_border (a : R) (r c : ι → R) (A : Matrix ι ι R) :
    (border a r c A).charpoly = (X - C a) * A.charpoly -
      (fun i => C (r i)) ⬝ᵥ (adjugate (charmatrix A) *ᵥ fun i => C (c i)) := by
  rw [charpoly, charmatrix_border,
    det_border_of_isRegular _ _ _ _ A.charpoly_monic.isRegular]
  simp [charpoly, dotProduct, mulVec]

theorem border_correction_coeff (r c : ι → R) (A : Matrix ι ι R) (d : ℕ) :
    ((fun i => C (r i)) ⬝ᵥ (adjugate (charmatrix A) *ᵥ fun i => C (c i))).coeff d =
      ∑ k ∈ Icc (d + 1) (Fintype.card ι),
        A.charpoly.coeff k * borderMoment r c A (k - (d + 1)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, finsetSum_coeff, coeff_C_mul,
    coeff_mul_C, adjugate_charmatrix_coeff]
  simp only [borderMoment, dotProduct, mulVec, Finset.mul_sum, Finset.sum_mul]
  trans ∑ k ∈ Icc (d + 1) (Fintype.card ι), ∑ i, ∑ j,
    r i * (A.charpoly.coeff k * (A ^ (k - (d + 1))) i j * c j)
  · calc
      _ = ∑ i, ∑ k ∈ Icc (d + 1) (Fintype.card ι), ∑ j,
          r i * (A.charpoly.coeff k * (A ^ (k - (d + 1))) i j * c j) := by
        apply sum_congr rfl
        intro i _
        exact Finset.sum_comm
      _ = _ := Finset.sum_comm
  · apply sum_congr rfl
    intro k _
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring

theorem charpoly_border_coeff (a : R) (r c : ι → R) (A : Matrix ι ι R) (d : ℕ) :
    (border a r c A).charpoly.coeff d =
      (if d = 0 then 0 else A.charpoly.coeff (d - 1)) - a * A.charpoly.coeff d -
        ∑ k ∈ Icc (d + 1) (Fintype.card ι),
          A.charpoly.coeff k * borderMoment r c A (k - (d + 1)) := by
  rw [charpoly_border, coeff_sub, border_correction_coeff, sub_mul, coeff_sub, coeff_C_mul]
  congr 2
  cases d <;> simp

end Mathproof.MinimumGeneration.RankBerkowitz

-- Ported from LeanCanny/Algebra/BerkowitzCoefficients.lean
/-!
# A recursive reference for characteristic coefficients and the determinant

The bordered recurrence is specialized to the leading row and column of a
`Fin n` matrix. A structural recursion computes each characteristic coefficient
from smaller principal matrices and scalar matrix-power moments. Its constant
coefficient recovers the determinant, including the empty matrix.

This function is an algebraic correctness reference. Its recursion has linear
depth in the dimension; no complexity bound is claimed. `BerkowitzBalanced`
supplies a transformation product and balanced entry recursion. An encoded
streamed implementation and its workspace bound remain separate obligations.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

def headTailEquiv (n : ℕ) : Unit ⊕ Fin n ≃ Fin (n + 1) where
  toFun
    | .inl _ => 0
    | .inr i => i.succ
  invFun := Fin.cases (.inl ()) (fun i => .inr i)
  left_inv x := by cases x <;> rfl
  right_inv i := by refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem charpoly_coeff_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d : ℕ) :
    A.charpoly.coeff d =
      (if d = 0 then 0 else (A.submatrix Fin.succ Fin.succ).charpoly.coeff (d - 1)) -
        A 0 0 * (A.submatrix Fin.succ Fin.succ).charpoly.coeff d -
        ∑ k ∈ Icc (d + 1) n, (A.submatrix Fin.succ Fin.succ).charpoly.coeff k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0)
            (A.submatrix Fin.succ Fin.succ) (k - (d + 1)) := by
  have heq : A.submatrix (headTailEquiv n) (headTailEquiv n) =
      border (A 0 0) (fun i => A 0 i.succ) (fun i => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ) := by
    ext (⟨⟩ | i) (⟨⟩ | j) <;> simp [border, headTailEquiv]
  have h := Matrix.charpoly_reindex (headTailEquiv n).symm A
  change (A.submatrix (headTailEquiv n) (headTailEquiv n)).charpoly = A.charpoly at h
  rw [heq] at h
  rw [← h, charpoly_border_coeff]
  simp only [Fintype.card_fin]

def coefficients : {n : ℕ} → Matrix (Fin n) (Fin n) R → ℕ → R
  | 0, _, d => if d = 0 then 1 else 0
  | n + 1, A, d =>
      let D := A.submatrix Fin.succ Fin.succ
      (if d = 0 then 0 else coefficients D (d - 1)) - A 0 0 * coefficients D d -
        ∑ k ∈ Icc (d + 1) n, coefficients D k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1))

theorem coefficients_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : ℕ) :
    coefficients A d = A.charpoly.coeff d := by
  induction n generalizing d with
  | zero => simp [coefficients, coeff_one]
  | succ n ih =>
      rw [coefficients, charpoly_coeff_succ]
      simp_rw [ih]

def determinant {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R := (-1) ^ n * coefficients A 0

theorem determinant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : determinant A = A.det := by
  rw [determinant, coefficients_eq, Matrix.det_eq_sign_charpoly_coeff]
  simp only [Fintype.card_fin]

end Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz

-- Ported from LeanCanny/Algebra/BerkowitzTransform.lean
/-!
# Linear transformations of characteristic coefficients

All coefficient vectors are padded to a common width and indexed in ascending
degree. Adding the leading row and column acts by an upper Hessenberg matrix:
one shifted diagonal, the leading scalar on the diagonal, and scalar power
moments above it. The transformation entries use only the input matrix and its
smaller principal block, not any characteristic coefficients.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
open Matrix Polynomial Finset

variable {R : Type*} [CommRing R]

def coefficientKernel {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (d k : ℕ) : R :=
  (if k + 1 = d then 1 else 0) - (if k = d then A 0 0 else 0) -
    if d < k ∧ k ≤ n then
      borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ) (k - (d + 1))
    else 0

def transformation {n : ℕ} (w : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin w) (Fin w) R := fun d k => coefficientKernel A d.val k.val

def coefficientVector {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) : Fin w → R :=
  fun i => A.charpoly.coeff i.val

theorem sum_shift (f : ℕ → R) (w d : ℕ) (hd : d < w) :
    (∑ k ∈ range w, (if k + 1 = d then (1 : R) else 0) * f k) =
      if d = 0 then 0 else f (d - 1) := by
  by_cases hz : d = 0
  · simp [hz]
  · have heq (k : ℕ) : k + 1 = d ↔ k = d - 1 := by omega
    simp only [heq, ite_mul, one_mul, zero_mul]
    simp [hz, show d - 1 < w by omega]

theorem sum_kernel {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (w d : ℕ) (hn : n < w) (hd : d < w) :
    (∑ k ∈ range w, coefficientKernel A d k *
      (A.submatrix Fin.succ Fin.succ).charpoly.coeff k) = A.charpoly.coeff d := by
  let D := A.submatrix Fin.succ Fin.succ
  have hfilter : {k ∈ range w | d < k ∧ k ≤ n} = Icc (d + 1) n := by
    ext k
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  simp only [coefficientKernel, sub_mul, sum_sub_distrib]
  rw [sum_shift _ w d hd]
  have hdiag : (∑ k ∈ range w, (if k = d then A 0 0 else 0) * D.charpoly.coeff k) =
      A 0 0 * D.charpoly.coeff d := by simp [ite_mul, hd]
  have hmoment : (∑ k ∈ range w, (if d < k ∧ k ≤ n then
      borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1)) else 0) *
      D.charpoly.coeff k) = ∑ k ∈ Icc (d + 1) n,
        D.charpoly.coeff k *
          borderMoment (fun i => A 0 i.succ) (fun i => A i.succ 0) D (k - (d + 1)) := by
    simp only [ite_mul, zero_mul, ← sum_filter, hfilter]
    apply sum_congr rfl
    intro k _
    exact mul_comm _ _
  rw [hdiag, hmoment, charpoly_coeff_succ]

theorem transformation_mulVec {n w : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (hn : n < w) :
    transformation w A *ᵥ coefficientVector w (A.submatrix Fin.succ Fin.succ) =
      coefficientVector w A := by
  funext d
  change (∑ k : Fin w, coefficientKernel A d.val k.val *
    (A.submatrix Fin.succ Fin.succ).charpoly.coeff k.val) = A.charpoly.coeff d.val
  rw [Fin.sum_univ_eq_sum_range (fun k => coefficientKernel A d.val k *
    (A.submatrix Fin.succ Fin.succ).charpoly.coeff k)]
  exact sum_kernel A w d.val hn d.isLt

end Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz

-- Ported from LeanCanny/Algebra/BerkowitzProduct.lean
/-!
# The determinant as an entry of a transformation product

The coefficient transformations of successive trailing principal matrices act
on the constant polynomial 1. Their ordered product contains every
characteristic coefficient in its first column. The determinant is its signed
top-left entry. Padding gives square matrices of one common width, enabling
balanced multiplication without storing the intermediate coefficient vectors.
This file specifies the factors as a list; an encoded evaluator must supply
uniform factor access without materializing that list.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
open Matrix Polynomial

variable {R : Type*} [CommRing R]

def factors (w : ℕ) : {n : ℕ} → Matrix (Fin n) (Fin n) R → List (Matrix (Fin w) (Fin w) R)
  | 0, _ => []
  | _ + 1, A => transformation w A :: factors w (A.submatrix Fin.succ Fin.succ)

theorem factors_length {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    (factors w A).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [factors, ih]

theorem factors_prod_mulVec {n w : ℕ} (A : Matrix (Fin n) (Fin n) R) (hn : n ≤ w) :
    (factors w A).prod *ᵥ (fun i : Fin w => if i.val = 0 then 1 else 0) =
      coefficientVector w A := by
  induction n with
  | zero =>
      funext i
      simp [factors, coefficientVector, coeff_one]
  | succ n ih =>
      rw [factors, List.prod_cons, ← Matrix.mulVec_mulVec, ih _ (by omega)]
      exact transformation_mulVec A (by omega)

theorem factors_prod_entry {n w : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hn : n ≤ w) (hw : 0 < w) (d : Fin w) :
    (factors w A).prod d ⟨0, hw⟩ = A.charpoly.coeff d.val := by
  have h := congrArg (fun v : Fin w → R => v d) (factors_prod_mulVec A hn)
  have heq (i : Fin w) : i.val = 0 ↔ i = ⟨0, hw⟩ := by simp [Fin.ext_iff]
  simpa [Matrix.mulVec, dotProduct, heq, coefficientVector] using h

theorem det_eq_factors_prod_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    A.det = (-1) ^ n * (factors (n + 1) A).prod 0 0 := by
  have h := factors_prod_entry (w := n + 1) A (by omega) (by omega) (0 : Fin (n + 1))
  calc
    A.det = (-1) ^ n * A.charpoly.coeff 0 := by
      simpa only [Fintype.card_fin] using Matrix.det_eq_sign_charpoly_coeff A
    _ = (-1) ^ n * (factors (n + 1) A).prod 0 0 := congrArg ((-1 : R) ^ n * ·) h.symm

end Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz

-- Ported from LeanCanny/Algebra/MatrixPowerEntry.lean
/-!
# Balanced recursion for a matrix-power entry

At height `h`, an entry of `A^e` is split into entries of the powers with
exponents `e/2` and `e-e/2`. The result is correct whenever `e ≤ 2^h`.
Consequently the binary length of `e` supplies sufficient height. The matrix
is an entry function; none of its intermediate powers is stored.

`entry` specifies the recursive sums. The continuation machine in
`MatrixPowerMachine` streams those sums. The work recurrence counts that
machine's transitions, rather than assigning unit cost to an entire sum.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.MatrixPower

variable {R : Type*} [Semiring R] {n : ℕ}

def entry (A : Matrix (Fin n) (Fin n) R) : ℕ → ℕ → Fin n → Fin n → R
  | 0, e, i, j => if e = 0 then if i = j then 1 else 0 else if e = 1 then A i j else 0
  | h + 1, e, i, j =>
      if e = 0 then if i = j then 1 else 0
      else if e = 1 then A i j
      else ∑ k, entry A h (e / 2) i k * entry A h (e - e / 2) k j

theorem entry_eq_pow (A : Matrix (Fin n) (Fin n) R) (h e : ℕ)
    (he : e ≤ 2 ^ h) (i j : Fin n) : entry A h e i j = (A ^ e) i j := by
  induction h generalizing e i j with
  | zero =>
      have : e = 0 ∨ e = 1 := by simp only [pow_zero] at he; omega
      rcases this with rfl | rfl <;> simp [entry, Matrix.one_apply]
  | succ h ih =>
      by_cases hzero : e = 0
      · subst e; simp [entry, Matrix.one_apply]
      by_cases hone : e = 1
      · subst e; simp [entry]
      have hhalf : e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      have hrest : e - e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      simp only [entry, hzero, hone, ↓reduceIte]
      simp_rw [ih _ hhalf, ih _ hrest]
      rw [← Matrix.mul_apply, ← pow_add, Nat.add_sub_of_le (Nat.div_le_self e 2)]

theorem entry_size_eq_pow (A : Matrix (Fin n) (Fin n) R) (e : ℕ) (i j : Fin n) :
    entry A e.size e i j = (A ^ e) i j :=
  entry_eq_pow A e.size e (Nat.lt_size_self e).le i j

/-- Exact transition count from evaluating a query to returning its scalar.
The continuation after that return is not included. -/
def work (n : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h + 1, e =>
      if e ≤ 1 then 1
      else 1 + n * (work n h (e / 2) + work n h (e - e / 2) + 2)

theorem work_pos (n h e : ℕ) : 0 < work n h e := by
  cases h <;> simp only [work]
  · decide
  · split_ifs <;> omega

theorem work_le (n h e : ℕ) : work n h e ≤ (4 * n + 1) ^ h := by
  induction h generalizing e with
  | zero => simp [work]
  | succ h ih =>
      have hpos : 0 < (4 * n + 1) ^ h := pow_pos (by omega) _
      rw [work, pow_succ]
      split_ifs
      · nlinarith
      · have hl := ih (e / 2)
        have hr := ih (e - e / 2)
        nlinarith

theorem work_add_one_le_two_pow (n h e : ℕ) :
    work n h e + 1 ≤ 2 ^ ((n.size + 2) * h + 1) := by
  have hbase : 4 * n + 1 ≤ 2 ^ (n.size + 2) := by
    have hn := Nat.lt_size_self n
    calc
      _ ≤ 4 * 2 ^ n.size := by omega
      _ = _ := by rw [pow_add]; norm_num; exact Nat.mul_comm _ _
  have hw : work n h e ≤ 2 ^ ((n.size + 2) * h) :=
    (work_le n h e).trans
      ((Nat.pow_le_pow_left hbase h).trans_eq (pow_mul _ _ _).symm)
  have hp : 0 < 2 ^ ((n.size + 2) * h) := pow_pos (by decide) _
  rw [pow_succ]
  omega

end Mathproof.MinimumGeneration.RankBerkowitz.MatrixPower

-- Ported from LeanCanny/Algebra/MatrixProductEntry.lean
/-!
# Balanced access to an ordered matrix product

A matrix family is accessed by its natural-number position. A product interval
is represented by its start and length. Balanced entry recursion splits the
interval in half, preserving factor order and needing only the binary length
of the interval as recursion height. Finite sums here are mathematical
specifications. `LayeredMatrixMachine` reduces this ordered product to the
existing streamed power machine, with factor-access costs still explicit.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.MatrixProduct

variable {R : Type*} [Semiring R] {n : ℕ}

def product (A : ℕ → Matrix (Fin n) (Fin n) R) (s : ℕ) : ℕ → Matrix (Fin n) (Fin n) R
  | 0 => 1
  | e + 1 => A s * product A (s + 1) e

theorem product_add (A : ℕ → Matrix (Fin n) (Fin n) R) (s a b : ℕ) :
    product A s (a + b) = product A s a * product A (s + a) b := by
  induction a generalizing s with
  | zero => simp [product]
  | succ a ih =>
      simp only [Nat.succ_add, product]
      rw [ih]
      simp only [Matrix.mul_assoc, Nat.add_comm, Nat.add_left_comm]

theorem product_congr (A B : ℕ → Matrix (Fin n) (Fin n) R) (s t e : ℕ)
    (hab : ∀ k, k < e → A (s + k) = B (t + k)) : product A s e = product B t e := by
  induction e generalizing s t with
  | zero => rfl
  | succ e ih =>
      have hzero := hab 0 (by omega)
      simp only [Nat.add_zero] at hzero
      rw [product, product, hzero]
      congr 1
      apply ih
      intro k hk
      have h := hab (k + 1) (by omega)
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem product_getD (L : List (Matrix (Fin n) (Fin n) R)) :
    product (fun k => L[k]?.getD 1) 0 L.length = L.prod := by
  induction L with
  | nil => rfl
  | cons B L ih =>
      rw [List.length_cons, product]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      have h : product (fun k => (B :: L)[k]?.getD 1) 1 L.length =
          product (fun k => L[k]?.getD 1) 0 L.length := by
        apply product_congr
        intro k _
        simp [Nat.add_comm]
      rw [h, ih, List.prod_cons]

def entry (A : ℕ → Matrix (Fin n) (Fin n) R) : ℕ → ℕ → ℕ → Fin n → Fin n → R
  | 0, s, e, i, j =>
      if e = 0 then if i = j then 1 else 0 else if e = 1 then A s i j else 0
  | h + 1, s, e, i, j =>
      if e = 0 then if i = j then 1 else 0
      else if e = 1 then A s i j
      else ∑ k, entry A h s (e / 2) i k * entry A h (s + e / 2) (e - e / 2) k j

theorem entry_eq_product (A : ℕ → Matrix (Fin n) (Fin n) R) (h s e : ℕ)
    (he : e ≤ 2 ^ h) (i j : Fin n) : entry A h s e i j = product A s e i j := by
  induction h generalizing s e i j with
  | zero =>
      have : e = 0 ∨ e = 1 := by simp only [pow_zero] at he; omega
      rcases this with rfl | rfl <;> simp [entry, product, Matrix.one_apply]
  | succ h ih =>
      by_cases hz : e = 0
      · subst e; simp [entry, product, Matrix.one_apply]
      by_cases ho : e = 1
      · subst e; simp [entry, product]
      have hl : e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      have hr : e - e / 2 ≤ 2 ^ h := by rw [pow_succ] at he; omega
      simp only [entry, hz, ho, ↓reduceIte]
      simp_rw [ih _ _ hl, ih _ _ hr]
      rw [← Matrix.mul_apply, ← product_add, Nat.add_sub_of_le (Nat.div_le_self e 2)]

theorem entry_size_eq_product (A : ℕ → Matrix (Fin n) (Fin n) R) (s e : ℕ) (i j : Fin n) :
    entry A e.size s e i j = product A s e i j :=
  entry_eq_product A e.size s e (Nat.lt_size_self e).le i j

end Mathproof.MinimumGeneration.RankBerkowitz.MatrixProduct

-- Ported from LeanCanny/Algebra/BerkowitzBalanced.lean
/-!
# Balanced evaluation of characteristic coefficients

A factor accessor follows trailing principal blocks and returns only the
requested coefficient transformation. Balanced interval recursion then
computes a characteristic coefficient, and hence the determinant, at height
`n.size`. The accessor does not construct the full factor list.

This proves algebraic correctness and the recursion-height requirement.
`BerkowitzPower` reduces the outer product to the existing streamed power
machine. Uniform binary factor access, including trailing blocks and scalar
power moments with their workspace, is still required. In particular, no
complexity bound for the recursive factor accessor is asserted here.
-/

namespace Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
open Matrix

variable {R : Type*} [CommRing R]

def factorAt (w : ℕ) : {n : ℕ} → Matrix (Fin n) (Fin n) R → ℕ → Matrix (Fin w) (Fin w) R
  | 0, _, _ => 1
  | _ + 1, A, 0 => transformation w A
  | _ + 1, A, s + 1 => factorAt w (A.submatrix Fin.succ Fin.succ) s

theorem factors_getD {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) (s : ℕ) :
    (factors w A)[s]?.getD 1 = factorAt w A s := by
  induction n generalizing s with
  | zero => simp [factors, factorAt]
  | succ n ih => cases s <;> simp [factors, factorAt, ih]

theorem factor_product_eq {n : ℕ} (w : ℕ) (A : Matrix (Fin n) (Fin n) R) :
    MatrixProduct.product (factorAt w A) 0 n = (factors w A).prod := by
  have h := MatrixProduct.product_getD (factors w A)
  simpa only [factors_length, factors_getD] using h

theorem balanced_entry_eq_coeff {n w : ℕ} (A : Matrix (Fin n) (Fin n) R)
    (hn : n ≤ w) (hw : 0 < w) (d : Fin w) :
    MatrixProduct.entry (factorAt w A) n.size 0 n d ⟨0, hw⟩ = A.charpoly.coeff d.val := by
  rw [MatrixProduct.entry_size_eq_product, factor_product_eq]
  exact factors_prod_entry A hn hw d

def balancedCoefficient {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) : R :=
  MatrixProduct.entry (factorAt (n + 1) A) n.size 0 n d 0

theorem balancedCoefficient_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (d : Fin (n + 1)) :
    balancedCoefficient A d = A.charpoly.coeff d.val :=
  balanced_entry_eq_coeff A (by omega) (by omega) d

def balancedDeterminant {n : ℕ} (A : Matrix (Fin n) (Fin n) R) : R :=
  (-1) ^ n * balancedCoefficient A 0

theorem balancedDeterminant_eq {n : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    balancedDeterminant A = A.det := by
  rw [balancedDeterminant, balancedCoefficient_eq, Matrix.det_eq_sign_charpoly_coeff]
  simp only [Fintype.card_fin, Fin.val_zero]

end Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
