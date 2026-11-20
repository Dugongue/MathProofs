module
import all Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Correctness
public import Mathlib.LinearAlgebra.Matrix.Determinant.Bird.Defs
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

public section

/-! Coefficient-only Bird recurrence for characteristic polynomials in every characteristic. -/
namespace Mathproof.Problem17CharpolyBird
open Polynomial
open scoped Matrix Polynomial

variable {K : Type*} [Field K] {n : ℕ}

abbrev CoeffGrid (K : Type*) (n : ℕ) := Fin n → Fin n → ℕ → K

def entry (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (d : ℕ) : K :=
  (if i = j ∧ d = 1 then 1 else 0) - (if d = 0 then A i j else 0)

def timesEntry (a x y : K) (diagonal : Bool) : K :=
  (if diagonal then y else 0) - x * a

def previous (f : ℕ → K) : ℕ → K
  | 0 => 0
  | d + 1 => f d

theorem entry_eq (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) (d : ℕ) :
    entry A i j d = (A.charmatrix i j).coeff d := by
  rw [Matrix.charmatrix_apply, Polynomial.coeff_sub]
  by_cases h : i = j
  · subst j
    simp [entry, coeff_X, coeff_C, eq_comm]
  · simp [entry, h, coeff_C]

theorem timesEntry_eq (A : Matrix (Fin n) (Fin n) K) (p : K[X]) (i j : Fin n) (d : ℕ) :
    timesEntry (A i j) (p.coeff d) (previous p.coeff d) (decide (i = j)) =
      (p * A.charmatrix i j).coeff d := by
  by_cases h : i = j
  · subst j
    rw [Matrix.charmatrix_apply_eq, mul_sub, coeff_sub, coeff_mul_C]
    cases d <;> simp [timesEntry, previous, coeff_mul_X]
  · rw [Matrix.charmatrix_apply_ne A (i := i) (j := j) h, mul_neg, coeff_neg, coeff_mul_C]
    simp [timesEntry, h]

def step (A : Matrix (Fin n) (Fin n) K) (F : CoeffGrid K n) : CoeffGrid K n :=
  fun i j d =>
    let p := fun s => -∑ k ∈ Finset.Ioi i, F k k s
    timesEntry (A i j) (p d) (previous p d) (decide (i = j)) +
      ∑ k ∈ Finset.Ioi i,
        timesEntry (A k j) (F i k d) (previous (F i k) d) (decide (k = j))

theorem step_eq (A : Matrix (Fin n) (Fin n) K) (F : Matrix (Fin n) (Fin n) K[X])
    (i j : Fin n) (d : ℕ) :
    step A (fun i j d => (F i j).coeff d) i j d =
      (BirdDet.Spec.stepEntry A.charmatrix F i j).coeff d := by
  have hs (s : ℕ) :
      -∑ k ∈ Finset.Ioi i, (F k k).coeff s = (-∑ k ∈ Finset.Ioi i, F k k).coeff s := by
    simp [Polynomial.finsetSum_coeff]
  rw [BirdDet.Spec.stepEntry_eq, Matrix.of_apply, coeff_add]
  simp only [step, hs, timesEntry_eq, Polynomial.finsetSum_coeff]

def iter (A : Matrix (Fin n) (Fin n) K) : ℕ → CoeffGrid K n
  | 0 => entry A
  | t+1 => step A (iter A t)

theorem iter_eq (A : Matrix (Fin n) (Fin n) K) (t : ℕ) :
    iter A t = fun i j d => (((BirdDet.Spec.stepEntry A.charmatrix)^[t]) A.charmatrix i j).coeff d := by
  induction t with
  | zero => funext i j d; exact entry_eq A i j d
  | succ t ih =>
    funext i j d
    rw [iter, ih, Function.iterate_succ_apply']
    exact step_eq A _ i j d

def coeffs : (n : ℕ) → Matrix (Fin n) (Fin n) K → ℕ → K
  | 0, _ => fun d => if d = 0 then 1 else 0
  | t+1, A => fun d => (-1 : K)^t * iter A t 0 0 d

theorem coeffs_eq (A : Matrix (Fin n) (Fin n) K) (d : ℕ) :
    coeffs n A d = A.charpoly.coeff d := by
  rw [Matrix.charpoly, BirdDet.birdDetSpec_eq_det]
  cases n with
  | zero => simp [coeffs, coeff_one]
  | succ t =>
    rw [coeffs, BirdDet.Spec.birdDetSpec_succ, iter_eq]
    have hpow : (-1 : K[X])^t = C ((-1 : K)^t) := by simp
    rw [hpow, coeff_C_mul]

end Mathproof.Problem17CharpolyBird

#print axioms Mathproof.Problem17CharpolyBird.coeffs_eq
