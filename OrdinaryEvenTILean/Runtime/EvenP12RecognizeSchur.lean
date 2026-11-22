import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.Ring.GeomSum

set_option autoImplicit false

namespace EvenTI.LiveSpectral

open Matrix

variable {R κ : Type} [CommRing R] [CommRing κ]

/-- A geometric inverse in a nilpotent neighborhood of one. -/
def nearOneInverse (b : Nat) (x : R) : R :=
  ∑ i ∈ Finset.range b, (1-x)^i

theorem nearOneInverse_mul {b : Nat} {x : R} (h : (1-x)^b = 0) :
    nearOneInverse b x * x = 1 := by
  have hgeom := geom_sum_mul_neg (1-x) b
  simpa [nearOneInverse, sub_sub_cancel, h] using hgeom

private def firstSplit (n : Nat) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl ()) Sum.inr
  left_inv := by
    intro x
    cases x with
    | inl x => cases x; rfl
    | inr x => simp
  right_inv := by
    intro x
    refine Fin.cases ?_ (fun i => ?_) x
    · rfl
    · simp

def nearOneSchur (b : Nat) {n : Nat} (A : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => A i.succ j.succ - A i.succ 0 * nearOneInverse b (A 0 0) * A 0 j.succ

/-- Division-free determinant recursion used with truncation modulo a power
of the indeterminate. Each pivot inverse is computed by a fixed finite sum. -/
def nearOneDet (b : Nat) : {n : Nat} → Matrix (Fin n) (Fin n) R → R
  | 0, _ => 1
  | _+1, A => A 0 0 * nearOneDet b (nearOneSchur b A)

theorem nearOneSchur_residue (reduce : R →+* κ) (b : Nat) {n : Nat}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) R) (hA : A.map reduce = 1) :
    (nearOneSchur b A).map reduce = 1 := by
  ext i j
  have hp (i j : Fin (n+1)) : reduce (A i j) = (1 : Matrix _ _ κ) i j :=
    congrFun (congrFun hA i) j
  simp [nearOneSchur, hp, one_apply]

theorem nearOneDet_eq (reduce : R →+* κ) {b : Nat}
    (hNil : ∀ x, reduce x = 0 → x^b = 0) :
    ∀ {n : Nat} (A : Matrix (Fin n) (Fin n) R), A.map reduce = 1 →
      nearOneDet b A = A.det := by
  intro n
  induction n with
  | zero => intro A _; simp [nearOneDet]
  | succ n ih =>
    intro A hA
    let p := A 0 0
    let inv := nearOneInverse b p
    have hp : reduce p = 1 := by
      simpa [p,one_apply] using congrFun (congrFun hA 0) 0
    have hi : inv * p = 1 := nearOneInverse_mul (hNil (1-p) (by simp [hp]))
    let U : Matrix Unit Unit R := fun _ _ => p
    let V : Matrix Unit Unit R := fun _ _ => inv
    have hVU : V * U = 1 := by
      ext i j
      cases i
      cases j
      change (V*U) () () = (1 : Matrix Unit Unit R) () ()
      rw [Matrix.mul_apply]
      simpa [U,V] using hi
    have hUV : U * V = 1 := by
      ext i j
      cases i
      cases j
      change (U*V) () () = (1 : Matrix Unit Unit R) () ()
      rw [Matrix.mul_apply]
      simpa [U,V] using (mul_comm p inv).trans hi
    letI : Invertible U := ⟨V,hVU,hUV⟩
    let B : Matrix Unit (Fin n) R := fun _ j => A 0 j.succ
    let C : Matrix (Fin n) Unit R := fun i _ => A i.succ 0
    let D : Matrix (Fin n) (Fin n) R := fun i j => A i.succ j.succ
    have hBlock : A.submatrix (firstSplit n) (firstSplit n) = fromBlocks U B C D := by
      ext i j
      cases i <;> cases j <;> rfl
    have hSchur : D - C * (⅟ U) * B = nearOneSchur b A := by
      ext i j
      change (D - C * V * B) i j = _
      rw [Matrix.sub_apply, Matrix.mul_apply, Finset.univ_unique, Finset.sum_singleton, Matrix.mul_apply]
      simp [nearOneSchur,D,C,V,B,inv,p]
    have hPivot : U.det = p := by rw [Matrix.det_unique]
    rw [nearOneDet, ih _ (nearOneSchur_residue reduce b A hA),
      ← det_submatrix_equiv_self (firstSplit n) A, hBlock, det_fromBlocks₁₁, hSchur, hPivot]

#print axioms nearOneDet_eq

end EvenTI.LiveSpectral
