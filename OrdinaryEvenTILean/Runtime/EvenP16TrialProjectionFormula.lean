import EvenP15TrialAnchorProduct
import EvenP11InputCoordOrder

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace EvenTI.P16Trial

open EvenTI.Action EvenTI.Contract EvenTI.TrialProducer EvenTI.P15Trial
open Matrix
open scoped Matrix BigOperators

variable {K : Type} [Field K]

/-- In retained-mode-first order, each basis-column evaluation copies one
row coefficient on the matching block and is zero off that block. -/
theorem retainedProjectionCoefficient_eq {d n : ℕ}
    (i : Fin (d+1)) (ell : Coord (d+1) n → K)
    (u v b : Fin n) (w : Coord d n) :
    projectionCoefficients (rawRetainedProjection i ell) (u,v) (retainedMode i (b,w)) =
      if u=b then retainedForm i ell v w else 0 := by
  classical
  have hEntry (x : Coord d n) :
      retainedForm i (Pi.single (retainedMode i (b,w)) (1 : K)) u x =
        if u=b ∧ x=w then 1 else 0 := by
    change (Pi.single (retainedMode i (b,w)) (1 : K) : Coord (d+1) n → K) (retainedMode i (u,x)) = _
    simp only [Pi.single_apply,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  change (retainedForm i (Pi.single (retainedMode i (b,w)) (1 : K)) *
    (retainedForm i ell)ᵀ) u v = _
  simp only [Matrix.mul_apply,Matrix.transpose_apply,hEntry]
  by_cases h : u=b
  · rw [if_pos h,Finset.sum_eq_single w]
    · simp [h]
    · intro x _ hx
      simp [h,hx]
    · simp
  · simp [h]

private theorem mixedRow_lt {n s : ℕ} (u : Fin n) (v : Fin s) :
    u.val*s+v.val < n*s := by
  have hNext := Nat.mul_le_mul_right s (show u.val+1 ≤ n by omega)
  rw [Nat.add_mul] at hNext
  simp only [Nat.one_mul] at hNext
  omega

private theorem mixedRow_div {n s : ℕ} (u : Fin n) (v : Fin s) :
    (u.val*s+v.val)/s=u.val := by
  have hs : 0 < s := Nat.zero_lt_of_lt v.isLt
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ hs,Nat.div_eq_of_lt v.isLt,zero_add]

private theorem mixedRow_mod {n s : ℕ} (u : Fin n) (v : Fin s) :
    (u.val*s+v.val)%s=v.val := by
  simp [Nat.add_mod,Nat.mod_eq_of_lt v.isLt]

/-- The retained gather produces the transpose. This arithmetic bridge ties
the grid's integer calls directly to the exact projection coefficient matrix. -/
theorem retainedProjectionGrid_meaning {d n : ℕ} (i : Fin (d+1))
    (ell : Coord (d+1) n → K) (read out : ℕ → K)
    (hRead : ∀ (v : Fin n) (w : Coord d n),
      read ((inputCoordOrder n d w).val*n+v.val)=retainedForm i ell v w)
    (hOut : ∀ x < n*n, ∀ y < n*n^d,
      out (x*(n*n^d)+y)=if x/n=y/n^d then read ((y%n^d)*n+x%n) else 0) :
    ∀ (u v b : Fin n) (w : Coord d n),
      out ((u.val*n+v.val)*(n*n^d)+(b.val*n^d+(inputCoordOrder n d w).val)) =
        projectionCoefficients (rawRetainedProjection i ell) (u,v) (retainedMode i (b,w)) := by
  intro u v b w
  let z := inputCoordOrder n d w
  change out ((u.val*n+v.val)*(n*n^d)+(b.val*n^d+z.val)) = _
  rw [hOut _ (mixedRow_lt u v) _ (mixedRow_lt b z),mixedRow_div u v,mixedRow_div b z,
    mixedRow_mod u v,mixedRow_mod b z,retainedProjectionCoefficient_eq]
  change (if u.val=b.val then read ((inputCoordOrder n d w).val*n+v.val) else 0) = _
  rw [hRead]
  by_cases hb : u=b
  · simp [hb]
  · simp [hb, show u.val ≠ b.val from fun hv => hb (Fin.ext hv)]

#print axioms retainedProjectionCoefficient_eq
#print axioms retainedProjectionGrid_meaning
end EvenTI.P16Trial