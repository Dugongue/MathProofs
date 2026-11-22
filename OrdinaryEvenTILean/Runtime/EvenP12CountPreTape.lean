import EvenP12CountPreModes
import EvenP12CountPreRoute
import EvenP12CountPrePrefix

namespace EvenTI.P12CountPre

open EvenTI.Action EvenTI.Contract EvenTI.P10Oracle

set_option autoImplicit false
variable {K : Type} [Field K] [Fintype K] {q : Nat}

theorem positiveWords_unpositiveWords (x : List Nat) (hx : ∀ a ∈ x, 0 < a) :
    positiveWords (unpositiveWords x) = x := by
  induction x with
  | nil => rfl
  | cons a xs ih =>
    simp only [positiveWords,unpositiveWords,List.map_cons]
    have ha := Nat.succ_pred_eq_of_pos (hx a List.mem_cons_self)
    exact congrArg₂ List.cons ha (ih fun b hb => hx b (List.mem_cons_of_mem a hb))

theorem cut_positive (z : List Nat) : ∀ a ∈ (cut z).1, 0 < a := by
  induction z with
  | nil => simp [cut]
  | cons x z ih =>
    cases x with
    | zero => simp [cut]
    | succ x =>
      intro a ha
      simp only [cut,List.mem_cons] at ha
      rcases ha with rfl|ha
      · omega
      · exact ih a ha

theorem positiveWords_cut (z : List Nat) : positiveWords (unpositiveWords (cut z).1) = (cut z).1 :=
  positiveWords_unpositiveWords _ (cut_positive z)

theorem scalarDigit_positive (F : FieldEncoding K) (u : Kˣ) (a : Nat) :
    scalarDigit F u (a+1) = mulDigit F u a + 1 := by
  simp [scalarDigit,mulDigit]

theorem ofFn_prod {α : Type*} {d q : Nat} (f : Fin d → Fin q → α) :
    (List.ofFn fun i : Fin (d*q) => f (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) =
      (List.ofFn fun i : Fin d => List.ofFn (f i)).flatten := by
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext j
  have hk : i.val*q+j.val < d*q := by
    calc
      i.val*q+j.val < (i.val+1)*q := by rw [Nat.add_mul,Nat.one_mul]; omega
      _ ≤ d*q := Nat.mul_le_mul_right _ i.isLt
  have hx : finProdFinEquiv (i,j) = ⟨i.val*q+j.val,hk⟩ := by
    apply Fin.ext
    change j.val + q * i.val = i.val * q + j.val
    ac_rfl
  rw [← hx,Equiv.symm_apply_apply]

/-- A direct query-loop list on the immutable packed tape. The raw comparison
arms determine the matrix offset, without re-decoding a tensor. -/
def queryTape (F : FieldEncoding K) (enum : Fin q ≃ Kˣ) (z : List Nat)
    (e d n a : Nat) : List Nat :=
  (List.range d).flatMap fun i =>
    (List.ofFn enum).flatMap fun u =>
      modeQueryWords F u z e (i+1) (n+1) (a+i*(n*n)) (a+(i+1)*(n*n))

private theorem slice_append_of_le {α : Type*} (p b t : List α) (off k : Nat)
    (h : off+k ≤ b.length) :
    (((p ++ b ++ t).take (p.length+off+k)).drop (p.length+off)) = (b.drop off).take k := by
  rw [← List.take_drop,List.append_assoc,drop_len_append,List.take_drop,
    List.take_append_of_le_length h,← List.take_drop]

/-- The live header and the matrix bank produce the same bytes as the pure
oracle query codec. This statement is pointwise in the mode and unit. -/
theorem modeQueryWords_eq_packed (F : FieldEncoding K) (u : Kˣ)
    (p : Nat) (body tw suffix : List Nat) (n i : Nat)
    (hp : p ≤ body.length) (ht : 2+(i+1)*(n*n) ≤ tw.length) :
    let w := p :: body
    let z := positiveWords w ++ 0 :: (positiveWords tw ++ suffix)
    modeQueryWords F u z (p+1) (i+1) (n+1) (w.length+3+i*(n*n)) (w.length+3+(i+1)*(n*n)) =
    positiveWords ([p] ++ body.take p ++ [i,n] ++
      ((tw.drop (2+i*(n*n))).take (n*n)).map (mulDigit F u)) ++ [0] := by
  let w := p :: body
  let ctxHead := positiveWords w ++ [0]
  let z := positiveWords w ++ 0 :: (positiveWords tw ++ suffix)
  have hz : z = ctxHead ++ positiveWords tw ++ suffix := by simp [z,ctxHead,List.append_assoc]
  have hlen : ctxHead.length = w.length+1 := by simp [ctxHead,positiveWords]
  have hPrefix : (((z.take (p+1)).drop 1)) = positiveWords (body.take p) := by
    have h : p+1 ≤ (positiveWords w).length := by simp only [positiveWords,List.length_map,w,List.length_cons]; omega
    change ((z.take (p+1)).drop 1) = _
    rw [show z = positiveWords w ++ (0 :: (positiveWords tw ++ suffix)) from rfl,
      List.take_append_of_le_length h]
    simp [w,positiveWords]
  have hoff : 2+i*(n*n)+n*n ≤ (positiveWords tw).length := by
    simpa [positiveWords,Nat.add_mul,Nat.add_assoc] using ht
  have hMat := slice_append_of_le ctxHead (positiveWords tw) suffix (2+i*(n*n)) (n*n) hoff
  rw [← hz,hlen] at hMat
  have h₁ : w.length+1+(2+i*(n*n)) = w.length+3+i*(n*n) := by omega
  have h₂ : w.length+3+i*(n*n)+(n*n) = w.length+3+(i+1)*(n*n) := by rw [Nat.add_mul]; omega
  rw [h₁,h₂] at hMat
  change modeQueryWords F u z (p+1) (i+1) (n+1) (w.length+3+i*(n*n)) (w.length+3+(i+1)*(n*n)) = _
  unfold modeQueryWords
  rw [hPrefix,hMat]
  simp only [positiveWords,List.map_append,List.map_cons,List.map_nil,List.map_drop,List.map_take,
    List.map_map, Function.comp_def,scalarDigit_positive,Nat.succ_eq_add_one]

theorem queryTape_eq_packSegments (F : FieldEncoding K) (enum : Fin q ≃ Kˣ)
    (p : Nat) (body tw suffix rest : List Nat) (d n : Nat)
    (hbody : body.drop p = d :: n :: rest) (ht : tw.head? = some 2)
    (hlen : 2+d*(n*n) ≤ tw.length) :
    let w := p :: body
    let z := positiveWords w ++ 0 :: (positiveWords tw ++ suffix)
    queryTape F enum z (p+1) d n (w.length+3) = packSegments (preK F enum w tw) := by
  let w := p :: body
  let z := positiveWords w ++ 0 :: (positiveWords tw ++ suffix)
  have hp : p ≤ body.length := by
    have h := congrArg List.length hbody
    simp only [List.length_drop,List.length_cons] at h
    omega
  have hRange : List.range d = (List.finRange d).map Fin.val := by
    apply List.ext_getElem (by simp)
    intro j hj hj'
    simp only [List.getElem_range,List.getElem_map,List.getElem_finRange,Fin.val_cast]
  change queryTape F enum z (p+1) d n (w.length+3) = packSegments (preK F enum w tw)
  have hSize : (body.take p).length = p := by simp [hp]
  simp only [preK,w,hbody,ht,if_true,hSize]
  have hf := ofFn_prod (fun (i : Fin d) (j : Fin q) =>
    [p] ++ body.take p ++ [i.val,n] ++
      ((tw.drop (2+i.val*(n*n))).take (n*n)).map (mulDigit F (enum j)))
  rw [hf]
  unfold packSegments queryTape
  rw [hRange]
  simp only [List.ofFn_eq_map,List.flatMap_map,Function.comp_def,List.flatten_eq_flatMap,
    List.flatMap_assoc,List.flatMap_id]
  apply List.flatMap_congr
  intro i hi
  simp only [id_eq,List.flatMap_map]
  apply List.flatMap_congr
  intro u hu
  have hm : 2+(i.val+1)*(n*n) ≤ tw.length :=
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) 2).trans hlen
  exact modeQueryWords_eq_packed F (enum u) p body tw suffix n i hp hm

#print axioms queryTape_eq_packSegments
#print axioms modeQueryWords_eq_packed
#print axioms cut_positive
#print axioms ofFn_prod
end EvenTI.P12CountPre
