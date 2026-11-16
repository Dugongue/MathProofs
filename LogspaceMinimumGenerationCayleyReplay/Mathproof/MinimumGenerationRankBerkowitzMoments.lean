import Mathproof.MinimumGenerationRankBerkowitz

/-!
Address-based entries of the balanced Berkowitz factor matrices.
The tail offset is a numeric coordinate, and each power moment is evaluated
by the checked balanced entry algorithm.
-/

noncomputable section

namespace Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz

open Matrix Finset

variable {R : Type*} [CommRing R]

def momentEntry {n : Nat} (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (e : Nat) : R :=
  ∑ i : Fin n, ∑ j : Fin n, r i * (MatrixPower.entry A e.size e i j * c j)

theorem momentEntry_eq {n : Nat} (r c : Fin n → R) (A : Matrix (Fin n) (Fin n) R)
    (e : Nat) : momentEntry r c A e = borderMoment r c A e := by
  simp [momentEntry, borderMoment, Matrix.mulVec, dotProduct,
    MatrixPower.entry_size_eq_pow, Finset.mul_sum]

def momentFactor {n : Nat} (width : Nat) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    Matrix (Fin width) (Fin width) R := fun d k =>
  (if k.val + 1 = d.val then 1 else 0) - (if k.val = d.val then A 0 0 else 0) -
    if d.val < k.val ∧ k.val ≤ n then
      momentEntry (fun i => A 0 i.succ) (fun i => A i.succ 0)
        (A.submatrix Fin.succ Fin.succ) (k.val - (d.val + 1))
    else 0

theorem momentFactor_eq {n : Nat} (width : Nat)
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    momentFactor width A = transformation width A := by
  ext i j
  simp [momentFactor, transformation, coefficientKernel, momentEntry_eq]

/-- Address a principal window using a fixed matrix-entry source. -/
def sourceWindow (source : Nat → Nat → R) (length offset : Nat) :
    Matrix (Fin length) (Fin length) R :=
  fun i j => source (i.val + offset) (j.val + offset)

/-- Direct factor access by shifted input coordinates. -/
def offsetFactor (source : Nat → Nat → R) (width length offset stage : Nat) :
    Matrix (Fin width) (Fin width) R :=
  if stage < length then
    momentFactor width (sourceWindow source (length - stage - 1 + 1) (offset + stage))
  else 1

omit [CommRing R] in
private theorem sourceWindow_succ (source : Nat → Nat → R) (length offset : Nat) :
    (sourceWindow source (length + 1) offset).submatrix Fin.succ Fin.succ =
      sourceWindow source length (offset + 1) := by
  ext i j
  simp only [Matrix.submatrix_apply, sourceWindow, Fin.val_succ]
  have hi : i.val + 1 + offset = i.val + (offset + 1) := by omega
  have hj : j.val + 1 + offset = j.val + (offset + 1) := by omega
  rw [hi, hj]

theorem factorAt_sourceWindow (source : Nat → Nat → R) (width length offset stage : Nat) :
    factorAt width (sourceWindow source length offset) stage =
      offsetFactor source width length offset stage := by
  induction length generalizing offset stage with
  | zero => simp [factorAt, offsetFactor]
  | succ length ih =>
    cases stage with
    | zero => simp [factorAt, offsetFactor, momentFactor_eq]
    | succ stage =>
      rw [factorAt, sourceWindow_succ, ih]
      have hOffset : offset + 1 + stage = offset + (stage + 1) := by omega
      have hSize : length + 1 - (stage + 1) = length - stage := by omega
      unfold offsetFactor
      rw [hOffset, hSize]
      simp

def matrixSource {n : Nat} (A : Matrix (Fin n) (Fin n) R) (i j : Nat) : R :=
  if hi : i < n then
    if hj : j < n then A ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

theorem sourceWindow_matrixSource {n : Nat} (A : Matrix (Fin n) (Fin n) R) :
    sourceWindow (matrixSource A) n 0 = A := by
  ext i j
  simp [sourceWindow, matrixSource, i.isLt, j.isLt]

/-- The balanced coefficient formula with direct numeric factor addressing. -/
def offsetBalancedCoefficient {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (d : Fin (n + 1)) : R :=
  MatrixProduct.entry (offsetFactor (matrixSource A) (n + 1) n 0) n.size 0 n d 0

theorem offsetBalancedCoefficient_eq {n : Nat} (A : Matrix (Fin n) (Fin n) R)
    (d : Fin (n + 1)) : offsetBalancedCoefficient A d = A.charpoly.coeff d.val := by
  have hFactor : offsetFactor (matrixSource A) (n + 1) n 0 = factorAt (n + 1) A := by
    ext stage i j
    rw [← factorAt_sourceWindow, sourceWindow_matrixSource]
  rw [offsetBalancedCoefficient, hFactor]
  exact balancedCoefficient_eq A d

end Mathproof.MinimumGeneration.RankBerkowitz.Berkowitz
