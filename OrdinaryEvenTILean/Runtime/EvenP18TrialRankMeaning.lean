import EvenP18TrialRankBlocks
import EvenP14CutRankMeaning

set_option autoImplicit false
set_option maxHeartbeats 1700000

namespace EvenTI.P18Trial

open EvenTI.P17Trial

open EvenTI.Action EvenTI.Contract EvenTI.P12Compare EvenTI.P12ComparePrep
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (val)
open Mathproof.P15RecogIMPDot20261007 (qN)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

private theorem filter_flatMap {α β : Type} (l : List α) (f : α → Bool)
    (render : α → List β) :
    (l.filter f).flatMap render=l.flatMap (fun x => if f x then render x else []) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases ha : f a <;> simp [ha,ih]

private theorem val_finRange (n : ℕ) :
    (List.finRange n).map (fun i : Fin n => i.val)=List.range n := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

/-- The emitted sparse sequence of successful blocks is precisely the
reference list of retained-full-rank forms read from the same initial
basis bank, in coefficient-code order. -/
theorem rankedBlocks_eq_bankForms (D : FieldEncoding K) (F : FieldPresentation K)
    {d n c budget : ℕ} (hn : 0 < n) (σ : Env) (j : Fin 4)
    (render : (Coord (d+1) n → K) → List ℕ) :
    (List.range (cappedCutChoiceCount (Fintype.card K) c budget)).flatMap
      (rankedBlockWords D F (c := c) σ j render) =
    (bankForms (c := c) D (inputCoordOrder n (d+1)) (val F canonical qN.WS σ)
      ((outputBase j).value (n^(d+1))) budget rawRetainedFullRank).flatMap render := by
  let q := Fintype.card K
  by_cases hb : q^c ≤ budget
  · rw [show cappedCutChoiceCount q c budget=q^c from if_pos hb,←val_finRange (q^c),List.flatMap_map]
    unfold bankForms linearChoices coefficientChoices
    rw [if_pos hb,filter_flatMap,List.flatMap_map,List.flatMap_map]
    congr 1
    funext v
    have hForm : (∑ i, coefficients D c v i •
        cutBankBasis (inputCoordOrder n (d+1)) (val F canonical qN.WS σ)
          ((outputBase j).value (n^(d+1))) i) = cutIndexedForm D F (d:=d) (n:=n) σ j v := by
      funext x
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,cutBankBasis,readBasis,cutIndexedForm]
    have hv : v.val < Fintype.card K^c := v.isLt
    simp only [rankedBlockWords,hForm]
    cases hRank : rawRetainedFullRank (cutIndexedForm D F (d:=d) (n:=n) σ j v) with
    | false => simp [hv,hRank]
    | true => simp [hv,hRank,rawRetainedFullRank_ne_zero hn hRank]
  · rw [show cappedCutChoiceCount q c budget=0 from if_neg hb]
    simp [bankForms,linearChoices,coefficientChoices,hb,q]

#print axioms rankedBlocks_eq_bankForms
end EvenTI.P18Trial
