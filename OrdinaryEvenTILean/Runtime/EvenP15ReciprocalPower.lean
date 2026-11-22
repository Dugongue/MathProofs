import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathproof.Meta.Problem18PairBoundaryMatrixPower20261004

set_option autoImplicit false
set_option maxHeartbeats 2300000

namespace EvenTI.P15Execution

open scoped BigOperators Matrix

/-- The integer exponent used by the inverse machine. -/
def glCount (q m : ℕ) : ℕ := ∏ j : Fin m, (q^m-q^j.val)

@[simp] theorem glCount_zero (q : ℕ) : glCount q 0 = 1 := by simp [glCount]

theorem glCount_succ (q m : ℕ) :
    glCount q (m+1) = (glCount q m*q^m)*(q^(m+1)-1) := by
  unfold glCount
  rw [Fin.prod_univ_succ]
  simp only [Fin.val_zero,pow_zero,Fin.val_succ]
  have h (j : Fin m) : q^(m+1)-q^(j.val+1) = (q^m-q^j.val)*q := by
    rw [pow_succ q m,pow_succ q j.val,Nat.sub_mul]
  simp only [h,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  exact Nat.mul_comm _ _

theorem glCount_pos {q : ℕ} (hq : 1 < q) (m : ℕ) : 0 < glCount q m := by
  unfold glCount
  apply Finset.prod_pos
  intro j _
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right hq j.isLt)

theorem glCount_le (q m : ℕ) : glCount q m ≤ q^(m*m) := by
  rw [pow_mul]
  calc
    glCount q m ≤ ∏ _ : Fin m, q^m := Finset.prod_le_prod' fun _ _ => Nat.sub_le _ _
    _ = _ := by simp

variable {K : Type} [Field K] [Fintype K]

/-- Binary matrix powering with the group-order exponent computes the inverse
of every nonsingular matrix. The exponent has quadratic bit length. -/
theorem inverse_eq_glPower {m : ℕ} (A : Matrix (Fin m) (Fin m) K)
    (hA : IsUnit A) : A^(glCount (Fintype.card K) m-1) = A⁻¹ := by
  obtain ⟨u,rfl⟩ := hA
  let q := Fintype.card K
  let E := glCount q m
  have hp : 0 < E := glCount_pos Fintype.one_lt_card _
  have ho : (((u : (Matrix (Fin m) (Fin m) K)ˣ) : Matrix (Fin m) (Fin m) K)^E) = 1 := by
    have he : E = Nat.card (GL (Fin m) K) := (Matrix.card_GL_field (𝔽:=K) m).symm
    rw [he]
    exact (congrArg (fun z : (Matrix (Fin m) (Fin m) K)ˣ => (z : Matrix (Fin m) (Fin m) K))
      (pow_card_eq_one' (x:=u)))
  let A : Matrix (Fin m) (Fin m) K := u
  change A^(E-1)=A⁻¹
  have hstep : A^(E-1)*A = 1 := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ E)]
    exact ho
  calc
    A^(E-1) = (A^(E-1)*A)*A⁻¹ := by rw [mul_assoc,Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp (show IsUnit A from u.isUnit)),mul_one]
    _ = A⁻¹ := by rw [hstep,one_mul]

theorem glCount_fits (q m : ℕ) : q^(m*m+m+2) < 2^(q*(m*m+m+2)+1) := by
  have hq : q ≤ 2^q := (Nat.lt_two_pow_self (n:=q)).le
  have h := Nat.pow_le_pow_left hq (m*m+m+2)
  rw [←pow_mul] at h
  exact h.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- Reading the exponent's bits costs only a quadratic number of word operations. -/
theorem glExponent_size {q : ℕ} (hq : 1 < q) (m : ℕ) :
    Nat.size (glCount q m-1) ≤ q*(m*m+m+2)+1 := by
  apply Nat.size_le.mpr
  exact (Nat.sub_le _ _).trans_lt ((glCount_le q m).trans_lt
    ((Nat.pow_le_pow_right (by omega) (by omega : m*m ≤ m*m+m+2)).trans_lt (glCount_fits q m)))

#print axioms inverse_eq_glPower
#print axioms glCount_fits
end EvenTI.P15Execution