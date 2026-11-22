import EvenP19InstallCapture

set_option autoImplicit false
set_option maxHeartbeats 900000
namespace EvenTI.P19Install

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem at_flatMap_fixed {α β : Type} (render : α → List β) (w : ℕ)
    (xs : List α) (h : ∀ a ∈ xs, (render a).length=w) (i : ℕ) (hi : i<xs.length) :
    ((xs.flatMap render).drop (i*w)).take w=render xs[i] := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    cases i with
    | zero =>
      simp only [Nat.zero_mul,List.drop_zero,List.flatMap_cons,List.getElem_cons_zero]
      exact List.take_left' hx
    | succ i =>
      have hι : i<xs.length := by simpa using hi
      have he : (i+1)*w = (render x).length+i*w := by rw [Nat.add_mul,Nat.one_mul,hx,Nat.add_comm]
      rw [he,←List.drop_drop,List.flatMap_cons,List.drop_left]
      exact ih (fun y hy => h y (List.mem_cons_of_mem x hy)) i hι

/-- A physical read from the shared capture selects the indicated literal
form and coordinate, even with another capture appended after it. -/
theorem capturedFormLabel (D : FieldEncoding K) {d n : ℕ}
    (forms : List (Coord d n → K)) (prefixWords suffixWords bank : List ℕ) (count : ℕ)
    (h : bank.take count = prefixWords ++ forms.flatMap (cutFormWords D) ++ suffixWords)
    (i : Fin forms.length) (j : Fin (n^d)) :
    bank[prefixWords.length+i.val*n^d+j.val]? =
      some (D (forms[i.val] ((cutOrder d n).symm j))).val := by
  let w := n^d
  have hw (f : Coord d n → K) : (cutFormWords D f).length=w := by simp [cutFormWords,w]
  have bound : i.val*w+j.val < forms.length*w := by
    calc
      i.val*w+j.val < (i.val+1)*w := by rw [Nat.succ_mul]; exact Nat.add_lt_add_left j.isLt _
      _ ≤ forms.length*w := Nat.mul_le_mul_right _ i.isLt
  have hCount : prefixWords.length+forms.length*w ≤ count := by
    have hl := congrArg List.length h
    simp only [List.length_take,List.length_append,formWords_length] at hl
    have hle := Nat.min_le_left count bank.length
    dsimp only [w]
    omega
  have hI : prefixWords.length+i.val*w+j.val < count := by omega
  simp only [List.append_assoc] at h
  rw [← List.getElem?_take_of_lt hI,h,Nat.add_assoc prefixWords.length,
    ←List.getElem?_drop,List.drop_left,List.getElem?_append_left (by rw [formWords_length]; exact bound)]
  have hWindow := at_flatMap_fixed (cutFormWords D) w forms (fun a _ => hw a) i.val i.isLt
  have hElem := congrArg (fun ws : List ℕ => ws[j.val]?) hWindow
  rw [List.getElem?_take_of_lt j.isLt,List.getElem?_drop] at hElem
  rw [hElem]
  rw [cutFormWords,List.getElem?_ofFn,dif_pos j.isLt]

#print axioms capturedFormLabel
end EvenTI.P19Install


