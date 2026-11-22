import EvenP12CompareLiveCRTPadding

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace EvenTI.P14Recovery

open EvenTI.P12Compare
open scoped BigOperators Matrix

variable {M m n : ℕ} [NeZero M]

/-- Reuse one fixed-height system throughout the sequential coordinate scan. -/
noncomputable def fixPaddedCoordinates (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) : List (Fin n) → (Fin n → ZMod M) → ℕ → Option (Fin n → ZMod M)
  | [], w, _ => some w
  | i :: is, w, p => do
    let v ← recoverCoordinate (fixedCoordinateMatrix A p) (fixedCoordinateRhs b w p) i
    fixPaddedCoordinates A b is (Function.update w i v) (p+1)

private theorem appendSolutions {k : ℕ} (A : Matrix (Fin k) (Fin n) (ZMod M))
    (b : Fin k → ZMod M) (i : Fin n) (v : ZMod M) (x : Fin n → ZMod M) :
    (appendCoordinate A i).mulVec x = appendCoordinateRhs b v ↔ A.mulVec x = b ∧ x i = v := by
  constructor
  · intro h
    refine ⟨funext fun r => ?_,?_⟩
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct] using congrFun h r.castSucc
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul]
        using congrFun h (Fin.last k)
  · rintro ⟨h,hx⟩
    funext r
    refine Fin.lastCases ?_ (fun j => ?_) r
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct,ite_mul] using hx
    · simpa [appendCoordinate,appendCoordinateRhs,Matrix.mulVec,dotProduct] using congrFun h j

/-- Fixed-height padding has exactly the same outputs, including failure, as
successive appended-row recovery on every consecutively numbered suffix. -/
theorem fixPaddedCoordinates_eq (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (is : List (Fin n)) {k : ℕ} (p : ℕ)
    (w : Fin n → ZMod M) (C : Matrix (Fin k) (Fin n) (ZMod M)) (c : Fin k → ZMod M)
    (hseq : ∀ t : Fin is.length, (is.get t).val = p+t.val)
    (hc : ∀ x, C.mulVec x = c ↔ A.mulVec x = b ∧ ∀ j : Fin n, j.val < p → x j = w j) :
    fixPaddedCoordinates A b is w p = fixCoordinates M n is w C c := by
  induction is generalizing k p w with
  | nil => rfl
  | cons i is ih =>
    have hi : i.val = p := by simpa using hseq ⟨0,by simp⟩
    have htail (t : Fin is.length) : (is.get t).val = p+1+t.val := by
      have ht := hseq ⟨t.val+1,by simpa using t.isLt⟩
      change (is.get t).val = p+(t.val+1) at ht
      omega
    have hrecover := recoverCoordinate_congr_solutions (fixedCoordinateMatrix A p) C
      (fixedCoordinateRhs b w p) c i (fun x => (fixedCoordinate_solutions A b w x p).trans (hc x).symm)
    rw [fixPaddedCoordinates,fixCoordinates,hrecover]
    cases h : recoverCoordinate C c i with
    | none => rfl
    | some v =>
      change fixPaddedCoordinates A b is (Function.update w i v) (p+1) =
        fixCoordinates M n is (Function.update w i v) (appendCoordinate C i) (appendCoordinateRhs c v)
      apply ih (p+1) _ _ _ htail
      intro x
      rw [appendSolutions,hc]
      constructor
      · rintro ⟨⟨ha,hprev⟩,hnew⟩
        refine ⟨ha,fun j hj => ?_⟩
        by_cases he : j = i
        · subst j
          simpa using hnew
        · have hne : j.val ≠ i.val := fun h => he (Fin.ext h)
          rw [Function.update_of_ne he]
          exact hprev j (by omega)
      · rintro ⟨ha,hprev⟩
        refine ⟨⟨ha,fun j hj => ?_⟩,?_⟩
        · have he : j ≠ i := fun he => by subst j; omega
          simpa [Function.update_of_ne he] using hprev j (by omega)
        · simpa using hprev i (by omega)

theorem fixPaddedCoordinates_start (A : Matrix (Fin m) (Fin n) (ZMod M))
    (b : Fin m → ZMod M) (w : Fin n → ZMod M) :
    fixPaddedCoordinates A b (List.finRange n) w 0 = fixCoordinates M n (List.finRange n) w A b := by
  apply fixPaddedCoordinates_eq
  · simp
  · simp

#print axioms fixPaddedCoordinates_eq
#print axioms fixPaddedCoordinates_start
end EvenTI.P14Recovery