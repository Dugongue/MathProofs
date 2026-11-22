import EvenP19InstallNativePair
import EvenP16InvertCutBank
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace EvenTI.P19Install

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P17Trial EvenTI.P18Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def pairListStart (right : Bool) : String :=
  if right then "P37#even.form.right-start" else "even.pair.list.left-start"

def pairListIndex (right : Bool) : String :=
  if right then "even.pair.list.right-index" else "even.pair.list.left-index"

def setPairWindow (right : Bool) : Com :=
  .assign (pairFormFrom right)
    (.add (.var (pairListStart right)) (.mul (.var (pairListIndex right)) (.var publicFormLength)))

theorem setPairWindow_run {B base idx w : ℕ} {s : Env} (right : Bool)
    (hBase : s.vars (pairListStart right)=base) (hIdx : s.vars (pairListIndex right)=idx)
    (hWidth : s.vars publicFormLength=w)
    (hi : idx<B) (hw : w<B) (hFit : base+idx*w<B) :
    Run B (setPairWindow right) s (s.setVar (pairFormFrom right) (base+idx*w)) 6 := by
  have hMul := evalB_bin (op:=.mul) (ev_var hIdx hi) (ev_var hWidth hw)
    (show idx*w<B by omega)
  have hE := ev_add (ev_var hBase (show base<B by omega)) hMul hFit
  exact Run.assign (x:=pairFormFrom right) hE

noncomputable def replayCapturedPair (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (setPairWindow false) (.seq (setPairWindow true) (scatterFormPair D F))

/-- Select two list indices from the physical capture, compute both word
addresses, and install the indicated ordered pair of forms. -/
theorem replayCapturedPair_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n dstL dstR : ℕ} {s : Env}
    (formsL formsR : List (Coord d n → K)) (prefixWords : List ℕ)
    (i : Fin formsL.length) (j : Fin formsR.length)
    (hn : 0 < n) (hnB : n < B) (hdB : d < B) (hmB : n^d < B)
    (hQ : Fintype.card K ≤ B) (hApart : dstL+n^d≤dstR) (hFit : dstR+n^d≤S)
    (hSize : s.vars formOutputCursor≤B)
    (hBank : (s.arrs formOutputTape).take (s.vars formOutputCursor) =
      prefixWords++formsL.flatMap (cutFormWords D)++formsR.flatMap (cutFormWords D))
    (hi : i.val<B) (hj : j.val<B)
    (hs : Slots F canonical qN.WS S B s)
    (hBaseL : s.vars (pairListStart false)=prefixWords.length)
    (hBaseR : s.vars (pairListStart true)=prefixWords.length+formsL.length*n^d)
    (hIdxL : s.vars (pairListIndex false)=i.val) (hIdxR : s.vars (pairListIndex true)=j.val)
    (hDstL : s.vars (pairFormTo false)=dstL) (hDstR : s.vars (pairFormTo true)=dstR)
    (hLen : s.vars publicFormLength=n^d) (hModes : s.vars emitFormModes=d)
    (hRadix : s.vars reverseDigitBase=n) :
    ∃ t, Run B (replayCapturedPair D F) s t (12+2*(4+scatterPublicFormCost F d (n^d))) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ x, val F canonical qN.WS t (dstL+(inputCoordOrder n d x).val)=formsL[i.val] x) ∧
      (∀ x, val F canonical qN.WS t (dstR+(inputCoordOrder n d x).val)=formsR[j.val] x) ∧
      (∀ k, (k < dstL ∨ dstL+n^d ≤ k) → (k < dstR ∨ dstR+n^d ≤ k) →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r≠pairFormFrom false → r≠pairFormFrom true → r∉pairReadScratch → t.vars r=s.vars r) ∧
      t.arrs formOutputTape=s.arrs formOutputTape ∧ t.inp=s.inp ∧ t.out=s.out := by
  let m := n^d
  let a := prefixWords.length
  let b := a+formsL.length*m
  let p := a+i.val*m
  let q := b+j.val*m
  have hTotal : b+formsR.length*m≤B := by
    have hl := congrArg List.length hBank
    simp only [List.length_take,List.length_append,formWords_length] at hl
    have ht := Nat.min_le_left (s.vars formOutputCursor) (s.arrs formOutputTape).length
    change a+formsL.length*m+formsR.length*m≤B
    change min (s.vars formOutputCursor) (s.arrs formOutputTape).length =
      a+formsL.length*m+formsR.length*m at hl
    omega
  have hIL := Nat.mul_le_mul_right m i.isLt
  have hJR := Nat.mul_le_mul_right m j.isLt
  rw [Nat.succ_mul] at hIL hJR
  have hp : p+m≤B := by dsimp only [p,b] at *; omega
  have hq : q+m≤B := by dsimp only [q] at *; omega
  have hm : 0 < m := pow_pos hn _
  let u := s.setVar (pairFormFrom false) p
  let v := u.setVar (pairFormFrom true) q
  have r₁ : Run B (setPairWindow false) s u 6 :=
    setPairWindow_run false hBaseL hIdxL hLen hi hmB (by change p<B; omega)
  have r₂ : Run B (setPairWindow true) u v 6 :=
    setPairWindow_run true (show u.vars (pairListStart true)=b from hBaseR)
      (show u.vars (pairListIndex true)=j.val from hIdxR)
      (show u.vars publicFormLength=m from hLen) hj hmB (by change q<B; omega)
  have hv : Slots F canonical qN.WS S B v :=
    Slots.setVar F canonical (Slots.setVar F canonical hs (by decide) (by decide) _)
      (by decide) (by decide) _
  have hReadL (k : Fin m) : (v.arrs formOutputTape)[p+k.val]? =
      some (D (formsL[i.val] ((cutOrder d n).symm k))).val :=
    capturedFormLabel D formsL prefixWords (formsR.flatMap (cutFormWords D))
      (s.arrs formOutputTape) (s.vars formOutputCursor) hBank i k
  have hRBank : (s.arrs formOutputTape).take (s.vars formOutputCursor) =
      (prefixWords++formsL.flatMap (cutFormWords D))++formsR.flatMap (cutFormWords D)++[] := by
    simpa only [List.append_nil,List.append_assoc] using hBank
  have hBaseLen : (prefixWords++formsL.flatMap (cutFormWords D)).length = b := by
    simp only [List.length_append,formWords_length,b,m,a]
  have hReadR (k : Fin m) : (v.arrs formOutputTape)[q+k.val]? =
      some (D (formsR[j.val] ((cutOrder d n).symm k))).val := by
    have h := capturedFormLabel D formsR (prefixWords++formsL.flatMap (cutFormWords D))
      [] (s.arrs formOutputTape) (s.vars formOutputCursor) hRBank j k
    rw [hBaseLen] at h
    exact h
  obtain ⟨t,rt,ht,hL,hR,hMem,hReg,hTape,hInp,hOut⟩ :=
    scatterFormPair_run D F formsL[i.val] formsR[j.val] hn hnB hdB hmB hQ hApart hFit hp hq hv
      (show v.vars (pairFormFrom false)=p from rfl) rfl
      (show v.vars (pairFormTo false)=dstL from hDstL) (show v.vars (pairFormTo true)=dstR from hDstR)
      (show v.vars publicFormLength=m from hLen) (show v.vars emitFormModes=d from hModes)
      (show v.vars reverseDigitBase=n from hRadix) hReadL hReadR
  refine ⟨t,(r₁.seq (r₂.seq rt)).mono (by omega),ht,hL,hR,?_,?_,hTape,hInp,hOut⟩
  · intro k hkL hkR
    exact (hMem k hkL hkR).trans ((val_setVar F canonical
      (by decide : pairFormFrom true≠qN.WS) u q k).trans
      (val_setVar F canonical (by decide : pairFormFrom false≠qN.WS) s p k))
  · intro r hfr htr hScratch
    exact (hReg r hScratch).trans (by simp [v,u,hfr,htr])

#print axioms setPairWindow_run
#print axioms replayCapturedPair_run
/-- Frame transfer from the replay's slot guarantee to an entire original
balanced cut placed below the two destination form banks. -/
theorem replay_preserves_lowerCut (F : FieldPresentation K) {l n base dstL dstR : ℕ} {s t : Env}
    (hRaw : base+(n*n^l)*(n*n^l)≤dstL) (hOrder : dstL≤dstR)
    (h : ∀ k, (k<dstL ∨ dstL+n^(l+1)≤k) → (k<dstR ∨ dstR+n^(l+1)≤k) →
      val F canonical qN.WS t k=val F canonical qN.WS s k) :
    EvenTI.P16Execution.cutSlotMatrix F t l n base = EvenTI.P16Execution.cutSlotMatrix F s l n base := by
  ext x y
  let m := n*n^l
  let i := (inputCoordOrder n (l+1) x).val
  let j := (inputCoordOrder n (l+1) y).val
  have hi : i < m := by simpa only [m,i,pow_succ'] using (inputCoordOrder n (l+1) x).isLt
  have hj : j < m := by simpa only [m,j,pow_succ'] using (inputCoordOrder n (l+1) y).isLt
  have hEdge : base+(i*m+j)<dstL := by
    have hh := Nat.mul_le_mul_right m hi
    rw [Nat.succ_mul] at hh
    change base+m*m≤dstL at hRaw
    omega
  exact h _ (Or.inl hEdge) (Or.inl (hEdge.trans_le hOrder))

#print axioms replay_preserves_lowerCut
end EvenTI.P19Install





