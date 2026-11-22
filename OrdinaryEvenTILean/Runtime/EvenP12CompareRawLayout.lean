import EvenP11InputCoordOrder

namespace EvenTI.P12Compare

open EvenTI.Action EvenTI.Contract

private theorem inputCoord_cast (n : ℕ) {a b : ℕ} (h : a = b) (x : Coord b n) :
    (inputCoordOrder n a (x ∘ Fin.cast h)).val = (inputCoordOrder n b x).val := by
  subst b
  simp only [Fin.cast_refl, Function.comp_id]

theorem inputCoord_val_succ (n d : ℕ) (x : Coord (d + 1) n) :
    (inputCoordOrder n (d + 1) x).val =
      (inputCoordOrder n d (Fin.tail x)).val + n ^ d * (x 0).val := rfl

/-- Each balanced-cut row starts at its raw mixed-radix address. -/
theorem inputCoord_append (n a b : ℕ) (x : Coord a n) (y : Coord b n) :
    (inputCoordOrder n (a + b) (Fin.append x y)).val =
      (inputCoordOrder n a x).val * n ^ b + (inputCoordOrder n b y).val := by
  induction a with
  | zero =>
    have hx : x = Fin.elim0 := by funext i; exact i.elim0
    rw [hx, Fin.elim0_append, inputCoord_cast]
    simp [inputCoordOrder]
  | succ a ih =>
    have h := Fin.append_cons (x 0) (Fin.tail x) y
    rw [Fin.cons_self_tail] at h
    rw [h, inputCoord_cast, inputCoord_val_succ, Fin.tail_cons, Fin.cons_zero, ih,
      inputCoord_val_succ, Nat.pow_add]
    ring

def cutAddress (n a b : ℕ) (x : Coord a n) (y : Coord b n) : ℕ :=
  (inputCoordOrder n a x).val * n ^ b + (inputCoordOrder n b y).val

theorem cutAddress_lt (n a b : ℕ) (x : Coord a n) (y : Coord b n) :
    cutAddress n a b x y < n ^ (a + b) := by
  rw [cutAddress, ← inputCoord_append]
  exact (inputCoordOrder n (a + b) (Fin.append x y)).isLt

variable {K : Type} [Field K] [Fintype K]

theorem tensorWords_getD_raw (F : FieldEncoding K) {d n : ℕ} (T : Tensor K d n)
    (x : Coord d n) :
    (tensorWords F T).getD (inputCoordOrder n d x).val 0 = (F (T x)).val := by
  rw [tensorWords_eq_inputCoordOrder, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
    dif_pos (inputCoordOrder n d x).isLt]
  simp

theorem tensorWords_getD_cut (F : FieldEncoding K) {a b n : ℕ}
    (T : Tensor K (a+b) n) (x : Coord a n) (y : Coord b n) :
    (tensorWords F T).getD (cutAddress n a b x y) 0 = (F (flatten T x y)).val := by
  rw [cutAddress, ← inputCoord_append]
  exact tensorWords_getD_raw F T (Fin.append x y)

theorem comparisonInput_source_cut (F : FieldEncoding K) {a b n : ℕ}
    (T S : Tensor K (a+b) n) (x : Coord a n) (y : Coord b n) :
    (comparisonInput F T S).getD (2 + cutAddress n a b x y) 0 = (F (flatten T x y)).val := by
  have hA := cutAddress_lt n a b x y
  have hT := tensorWords_length F T
  unfold comparisonInput
  rw [List.append_assoc]
  rw [show 2 + cutAddress n a b x y = cutAddress n a b x y + 1 + 1 by omega]
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
    ← List.getD_eq_getElem?_getD]
  exact tensorWords_getD_cut F T x y

theorem comparisonInput_target_cut (F : FieldEncoding K) {a b n : ℕ}
    (T S : Tensor K (a+b) n) (x : Coord a n) (y : Coord b n) :
    (comparisonInput F T S).getD (2 + (n^(a+b) + cutAddress n a b x y)) 0 =
      (F (flatten S x y)).val := by
  have hT := tensorWords_length F T
  unfold comparisonInput
  rw [List.append_assoc]
  rw [show 2 + (n^(a+b) + cutAddress n a b x y) =
    n^(a+b) + cutAddress n a b x y + 1 + 1 by omega]
  simp only [List.cons_append, List.nil_append, List.getD_cons_succ]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hT,
    Nat.add_sub_cancel_left, ← List.getD_eq_getElem?_getD]
  exact tensorWords_getD_cut F S x y

#print axioms comparisonInput_source_cut
#print axioms comparisonInput_target_cut

end EvenTI.P12Compare
