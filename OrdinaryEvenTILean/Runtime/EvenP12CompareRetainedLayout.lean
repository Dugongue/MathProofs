import EvenP12CompareRawLayout
import EvenNextRetainedCovariance

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract

/-- Insert the retained-mode digit into the raw mixed-radix column address. -/
def insertWordIndex (n base row col : ℕ) : ℕ :=
  ((col / base) * n + row) * base + col % base

private theorem retainedMode_zero (d n : ℕ) (x : Fin n) (u : Coord d n) :
    retainedMode (0 : Fin (d + 1)) (x,u) = Fin.cons x u := by
  simp [retainedMode, Fin.consEquiv]

private theorem retainedMode_succ (d n : ℕ) (i : Fin (d + 1)) (x : Fin n)
    (u : Coord (d + 1) n) :
    retainedMode i.succ (x,u) = Fin.cons (u 0) (retainedMode i (x,Fin.tail u)) := by
  have h := Fin.insertNth_succ_cons i x (u 0) (Fin.tail u)
  rw [Fin.cons_self_tail] at h
  exact h

private theorem insertWordIndex_add_high (n d i h x j : ℕ) (hn : 0 < n) (hi : i ≤ d) :
    insertWordIndex n (n^(d-i)) x (j + n^d * h) =
      insertWordIndex n (n^(d-i)) x j + n^(d+1) * h := by
  have hb : 0 < n^(d-i) := pow_pos hn _
  have hpower : n^i * n^(d-i) = n^d := by rw [← pow_add, Nat.add_sub_of_le hi]
  have hadd : j + n^d * h = j + (n^i * h) * n^(d-i) := by rw [← hpower]; ring
  unfold insertWordIndex
  rw [hadd, Nat.add_mul_div_right _ _ hb, Nat.add_mul_mod_self_right]
  rw [pow_succ, ← hpower]
  ring

/-- Every entry requested by a retained-mode row-major rank machine has an exact
address in the original tensor word list. -/
theorem inputCoord_retained (n d : ℕ) (hn : 0 < n) (i : Fin (d + 1))
    (x : Fin n) (u : Coord d n) :
    (inputCoordOrder n (d+1) (retainedMode i (x,u))).val =
      insertWordIndex n (n^(d-i.val)) x.val (inputCoordOrder n d u).val := by
  have hzero (s : ℕ) (v : Coord s n) :
      (inputCoordOrder n (s+1) (retainedMode (0 : Fin (s+1)) (x,v))).val =
        insertWordIndex n (n^s) x.val (inputCoordOrder n s v).val := by
    rw [retainedMode_zero, inputCoord_val_succ, Fin.tail_cons, Fin.cons_zero, insertWordIndex,
      Nat.div_eq_of_lt (inputCoordOrder n s v).isLt,
      Nat.mod_eq_of_lt (inputCoordOrder n s v).isLt]
    ring
  induction d with
  | zero =>
    have h : i = 0 := Fin.eq_zero i
    subst i
    exact hzero 0 u
  | succ d ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · exact hzero (d+1) u
    · rw [retainedMode_succ, inputCoord_val_succ, Fin.tail_cons, Fin.cons_zero,
        ih k (Fin.tail u), inputCoord_val_succ n d u]
      rw [show d+1-k.succ.val = d-k.val by simp]
      change _ = insertWordIndex n (n^(d-k.val)) x.val
        ((inputCoordOrder n d (Fin.tail u)).val + n^d * (u 0).val)
      exact (insertWordIndex_add_high n d k.val (u 0).val x.val
        (inputCoordOrder n d (Fin.tail u)).val hn (Nat.le_of_lt_succ k.isLt)).symm

variable {K : Type} [Field K] [Fintype K]

theorem tensorWords_getD_retained (F : FieldEncoding K) {d n : ℕ} (hn : 0 < n)
    (T : Tensor K (d+1) n) (i : Fin (d+1)) (x : Fin n) (u : Coord d n) :
    (tensorWords F T).getD
      (insertWordIndex n (n^(d-i.val)) x.val (inputCoordOrder n d u).val) 0 =
        (F (retainedForm i T x u)).val := by
  rw [← inputCoord_retained n d hn i x u]
  exact tensorWords_getD_raw F T (retainedMode i (x,u))

#print axioms inputCoord_retained
#print axioms tensorWords_getD_retained

end EvenTI.P12Compare
