import EvenP12CountPostNormalize
import EvenP12CountPostClassify

namespace EvenTI.P12CountPost

open EvenTI.P10Oracle
set_option autoImplicit false

private theorem cut_context (w tail : List ℕ) :
    cut ((cut w).1 ++ 0 :: tail) = ((cut w).1,tail) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    cases a with
    | zero => rfl
    | succ a => simpa [cut,ih]

theorem mapZ_cut_fst (g : List ℕ → List ℕ) (w : List ℕ) :
    (cut (mapZ g w)).1 = (cut w).1 := by
  cases w with
  | nil => rfl
  | cons a w =>
    rw [mapZ,cut_context]

theorem mapZ_cut_snd (g : List ℕ → List ℕ) (w : List ℕ) :
    (cut (mapZ g w)).2 = mapRest g (cut w).2 := by
  cases w with
  | nil => simp [mapZ, cut, mapRest]
  | cons a w =>
    rw [mapZ,cut_context]

def classifyFrame : List ℕ → List ℕ := mapZ (positiveCallback indicatorWords)

theorem classifyFrame_turingPolytime : Lax51.TuringPolytime.TuringPolytime classifyFrame :=
  classifiedAnswers_turingPolytime

theorem classifyFrame_answers (w : List ℕ) :
    (cut (classifyFrame w)).2 = packSegments ((unpackSegments (cut w).2).map indicatorWords) := by
  rw [classifyFrame,mapZ_cut_snd,mapRest_packUnpacked]

theorem postNormalize_classifyFrame {K : Type} [Field K] {q : ℕ}
    (enum : Fin q ≃ Kˣ) (w cmp : List ℕ) :
    postNormalize enum (classifyFrame w) cmp = postNormalize enum w cmp := by
  unfold postNormalize
  have hc : (cut (classifyFrame w)).1 = (cut w).1 := mapZ_cut_fst _ _
  have hd : postZSource (classifyFrame w) = postZSource w := by simp only [postZSource,hc]
  rw [hd]
  unfold postNormalizeParsed
  rw [hc,classifyFrame_answers,unpackSegments_packSegments]
  cases postZSource w with
  | nil => rfl
  | cons d rest =>
    by_cases h : cmp.head? = some 2 ∧ d ≤ (cut w).1.length
    · simp only [h,if_true]
      apply congrArg (encodeTable enum d)
      funext i u
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using
        indicator_getD (unpackSegments (cut w).2) (finProdFinEquiv (i,enum.symm u)).val
    · simp [h]

/-- The rows of the verified table consumer use exactly the unit order from
the oracle query generator, with row traversal reversed. -/
def indexedBits (q : ℕ) : ℕ → ℕ → (ℕ → ℕ) → List ℕ
  | 0, _, _ => []
  | d+1, i, g => indexedBits q d (i+1) g ++ (List.range q).map (fun k => g (q*i+k))

theorem rowWords_indexedBits {G : Type} [CommGroup G] [DecidableEq G] {q : ℕ}
    (enum : Fin q ≃ G) (d i : ℕ) (g : ℕ → Bool) :
    rowWords (tableRows enum d (fun (j : Fin d) u => g (q*(i+j.val)+(enum.symm u).val))) =
      indexedBits q d i (fun x => if g x then 1 else 0) := by
  induction d generalizing i with
  | zero => rfl
  | succ d ih =>
    rw [tableRows,indexedBits]
    have happ (a b : List (Fin q → ℕ)) : rowWords (a++b) = rowWords a ++ rowWords b := by
      simp [rowWords,List.flatMap_append]
    rw [happ]
    have he : (fun (j : Fin d) (u : G) => g (q*(i+j.succ.val)+(enum.symm u).val)) =
        (fun j u => g (q*((i+1)+j.val)+(enum.symm u).val)) := by
      funext j u
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
    rw [he,ih]
    congr 1
    simp [rowWords,List.finRange,List.map_ofFn]
    apply List.ext_get
    · simp
    · intro j hj hj'
      simp [List.getElem_ofFn]

#print axioms postNormalize_classifyFrame
#print axioms rowWords_indexedBits
end EvenTI.P12CountPost
