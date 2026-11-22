import EvenP16TrialProjectionFormula
import EvenP16TrialNativeProjection
import EvenP12CompareRetainedLayout

set_option autoImplicit false

namespace EvenTI.P16TrialNative

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P15Trial
open EvenTI.P16Trial (retainedProjectionCoefficient_eq)
open EvenTI.TrialProducer

private theorem inserted_div {n s b j : ℕ} (hs : 0 < s) :
    insertWordIndex n s b j / s = j/s*n+b := by
  unfold insertWordIndex
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hs,
    Nat.div_eq_of_lt (Nat.mod_lt j hs),zero_add]

private theorem mul_add_mod_eq {n a b : ℕ} (hb : b < n) :
    (a*n+b)%n=b := by simp [Nat.add_mod,Nat.mod_eq_of_lt hb]

private theorem mul_add_div_eq {n a b : ℕ} (hb : b < n) :
    (a*n+b)/n=a := by
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (by omega : 0 < n),Nat.div_eq_of_lt hb,zero_add]

theorem inserted_digit {n s b j : ℕ} (hs : 0 < s) (hb : b < n) :
    insertWordIndex n s b j / s % n = b := by
  rw [inserted_div hs,mul_add_mod_eq hb]

theorem change_inserted_digit {n s b j : ℕ} (hs : 0 < s) (hb : b < n) (k : ℕ) :
    changedDigit n s (insertWordIndex n s b j) k = insertWordIndex n s k j := by
  have hr : insertWordIndex n s b j % s = j%s := by
    unfold insertWordIndex
    rw [mul_add_mod_eq (Nat.mod_lt j hs)]
  rw [changedDigit,hr,inserted_div hs,mul_add_div_eq hb] <;> rfl

private theorem row_lt {n : ℕ} (u v : Fin n) :
    u.val*n+v.val < n*n := by
  have hu := u.isLt
  have hv := v.isLt
  have h := Nat.mul_le_mul_right n (show u.val+1 ≤ n by omega)
  simp only [Nat.add_mul,Nat.one_mul] at h
  omega

variable {K : Type} [Field K]

/-- Connect the physically produced coefficients to native cut-coordinate
order. Consequently the original flattening can enter the matrix product
directly in the same row-major bank, with no preliminary shuffle. -/
theorem nativeProjectionGrid_meaning {d n : ℕ} (i : Fin (d+1)) (hn : 0 < n)
    (ell : Coord (d+1) n → K) (read out : ℕ → K)
    (hRead : ∀ w : Coord (d+1) n, read (inputCoordOrder n (d+1) w).val=ell w)
    (hOut : ∀ x < n*n, ∀ y < n^(d+1),
      out (x*n^(d+1)+y)=
        if x/n=y/n^(d-i.val)%n then read (changedDigit n (n^(d-i.val)) y (x%n)) else 0) :
    ∀ (u v : Fin n) (x : Coord (d+1) n),
      out ((u.val*n+v.val)*n^(d+1)+(inputCoordOrder n (d+1) x).val) =
        projectionCoefficients (rawRetainedProjection i ell) (u,v) x := by
  intro u v x
  obtain ⟨⟨b,w⟩,rfl⟩ := (retainedMode i).surjective x
  rw [hOut _ (row_lt u v) _ (inputCoordOrder n (d+1) _).isLt,
    mul_add_div_eq v.isLt,mul_add_mod_eq v.isLt,
    inputCoord_retained n d hn i b w,
    inserted_digit (pow_pos hn _) b.isLt,
    change_inserted_digit (pow_pos hn _) b.isLt,
    ← inputCoord_retained n d hn i v w,
    hRead,retainedProjectionCoefficient_eq]
  by_cases hb : u=b
  · simp [hb,retainedForm]
  · have hne : u.val ≠ b.val := fun h => hb (Fin.ext h)
    simp [hb,hne]

#print axioms nativeProjectionGrid_meaning
end EvenTI.P16TrialNative