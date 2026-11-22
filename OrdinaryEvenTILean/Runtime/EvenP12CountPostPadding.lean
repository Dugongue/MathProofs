import EvenP12CountPostSource
import EvenP12CountPostGrid
import EvenP12CountPostEmitGrid

namespace EvenTI.P12CountPost

open EvenTI.P10Oracle
set_option autoImplicit false

theorem postDrop_cutSnd (xs : List ℕ) :
    xs.drop ((cut xs).1.length + 1) = (cut xs).2 := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases a with
    | zero => rfl
    | succ a => simpa only [cut, List.length_cons, List.drop_succ_cons] using ih

theorem postZSource_head (w : List ℕ) :
    (postZSource w).head? =
      if w.headD 0 < (cut w).1.length
      then some ((w.getD (w.headD 0) 0).pred) else none := by
  rw [postZSource_slice,List.head?_map,List.head?_drop,List.getElem?_take]
  by_cases h : w.headD 0 < (cut w).1.length
  · have h' := h.trans_le (postCutLength_le w)
    simp only [if_pos h,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem h',
      Option.getD_some,Option.map_some]
  · simp only [if_neg h,Option.map_none]
theorem pack_classified_address (xs : List (List ℕ)) (i : ℕ) :
    flagAt (packSegments (xs.map indicatorWords)) (2*i) =
      (if xs.getD i [] = [1] then 1 else 0) := by
  induction xs generalizing i with
  | nil => simp [flagAt, packSegments]
  | cons x xs ih =>
    have hpack : packSegments ((x::xs).map indicatorWords) =
        (if x = [1] then 2 else 1) :: 0 :: packSegments (xs.map indicatorWords) := by
      by_cases hx : x = [1] <;> simp [List.map_cons, packSegments, indicatorWords, positiveWords,hx]
    rw [hpack]
    cases i with
    | zero => by_cases hx : x = [1] <;> simp [flagAt, hx, List.getD_eq_getElem?_getD]
    | succ i =>
      rw [show 2*(i+1) = (2*i)+1+1 by omega]
      simp [flagAt, List.getD_eq_getElem?_getD, List.getElem?_cons_succ] at ih ⊢
      exact ih i

theorem classified_address (w : List ℕ) (i : ℕ) :
    flagAt (classifyFrame w) ((cut (classifyFrame w)).1.length+1+2*i) =
      (if (unpackSegments (cut w).2).getD i [] = [1] then 1 else 0) := by
  have h (z : List ℕ) (p k : ℕ) : flagAt z (p+k) = flagAt (z.drop p) k := by
    simp [flagAt, List.getD_eq_getElem?_getD,List.getElem?_drop]
  rw [h,postDrop_cutSnd,classifyFrame_answers,pack_classified_address]

/-- The final numerical representation uses the raw arity word and bounded
addresses in the singleton-classified answer stream. -/
def normalizeClassified (q : ℕ) (w : List ℕ) : List ℕ :=
  let stop := (cut w).1.length
  let p := w.headD 0
  if p < stop then
    let d := (w.getD p 0).pred
    if d ≤ stop then d :: indexedBits q d 0 (fun j => flagAt w (stop+1+2*j))
    else []
  else []

theorem postNormalize_eq_normalizeClassified {K : Type} [Field K] {q : ℕ}
    (enum : Fin q ≃ Kˣ) (w : List ℕ) :
    postNormalize enum w [2] = normalizeClassified q (classifyFrame w) := by
  classical
  rw [← postNormalize_classifyFrame]
  let z := classifyFrame w
  change postNormalize enum z [2] = normalizeClassified q z
  unfold postNormalize postNormalizeParsed normalizeClassified
  cases hs : postZSource z with
  | nil =>
    have he : ¬ z.headD 0 < (cut z).1.length := by
      intro hc
      have hh := postZSource_head z
      rw [hs,if_pos hc] at hh
      cases hh
    simp only [if_neg he]
  | cons d rest =>
    have he := postZSource_head z
    rw [hs] at he
    have hp : z.headD 0 < (cut z).1.length := by
      by_contra hc
      rw [if_neg hc] at he
      cases he
    have hd : (z.getD (z.headD 0) 0).pred = d := by
      rw [if_pos hp] at he
      exact Option.some.inj he.symm
    simp only [if_pos hp,hd]
    by_cases h : d ≤ (cut z).1.length
    · simp only [if_pos h,List.head?_cons,eq_self_iff_true,true_and]
      unfold encodeTable
      congr 1
      have hg := rowWords_indexedBits enum d 0
        (fun k => decide (((unpackSegments (cut w).2).getD k []) = [1]))
      have hr : (fun (j : Fin d) (u : Kˣ) =>
          decide ((unpackSegments (cut z).2).getD (finProdFinEquiv (j,enum.symm u)).val [] = [1])) =
          (fun (j : Fin d) (u : Kˣ) =>
          decide (((unpackSegments (cut w).2).getD (q*(0+j.val)+(enum.symm u).val) []) = [1])) := by
        funext j u
        rw [show (cut z).2 = packSegments ((unpackSegments (cut w).2).map indicatorWords) from classifyFrame_answers w,
          unpackSegments_packSegments]
        have hi : (finProdFinEquiv (j,enum.symm u)).val = q*(0+j.val)+(enum.symm u).val := by
          change (enum.symm u).val + q*j.val = _
          simp only [Nat.zero_add]
          omega
        rw [hi]
        apply Bool.eq_iff_iff.mpr
        simpa only [decide_eq_true_eq] using
          indicator_getD (unpackSegments (cut w).2) (q*(0+j.val)+(enum.symm u).val)
      rw [hr,hg]
      congr 1
      funext j
      simpa only [decide_eq_true_eq] using (classified_address w j).symm
    · simp only [List.head?_cons,eq_self_iff_true,true_and,if_neg h]

#print axioms postZSource_head
#print axioms pack_classified_address
#print axioms postNormalize_eq_normalizeClassified
end EvenTI.P12CountPost
