import EvenP18TrialFormScatterLoop
import EvenP19InstallWindow

set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 13000

namespace EvenTI.P19Install

open EvenTI.Action EvenTI.Contract EvenTI.P10Scan EvenTI.P17Trial EvenTI.P18Trial EvenTI.P16Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def pairFormFrom (right : Bool) : String :=
  if right then "even.pair.form.right-from" else "even.pair.form.left-from"

def pairFormTo (right : Bool) : String :=
  if right then "even.pair.form.right-to" else "even.pair.form.left-to"

def pairReadScratch : List String :=
  [publicFormStart,publicFormTarget,publicFormCursor] ++ scatterScratch

noncomputable def scatterPairSide (D : FieldEncoding K) (F : FieldPresentation K) (right : Bool) : Com :=
  .seq (.assign publicFormStart (.var (pairFormFrom right)))
    (.seq (.assign publicFormTarget (.var (pairFormTo right)))
      (scatterPublicForm D F formOutputTape))

theorem scatterPairSide_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n start dest : ℕ} {s : Env} (right : Bool) (form : Coord d n → K)
    (hn : 0 < n) (hnB : n < B) (hdB : d < B) (hmB : n^d < B)
    (hQ : Fintype.card K ≤ B) (hFit : dest+n^d ≤ S) (hReadFit : start+n^d ≤ B)
    (hs : Slots F canonical qN.WS S B s)
    (hStart : s.vars (pairFormFrom right)=start) (hDest : s.vars (pairFormTo right)=dest)
    (hLen : s.vars publicFormLength=n^d)
    (hModes : s.vars emitFormModes=d) (hRadix : s.vars reverseDigitBase=n)
    (hRead : ∀ j : Fin (n^d), (s.arrs formOutputTape)[start+j.val]? =
      some (D (form ((cutOrder d n).symm j))).val) :
    ∃ t, Run B (scatterPairSide D F right) s t (4+scatterPublicFormCost F d (n^d)) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ x, val F canonical qN.WS t (dest+(inputCoordOrder n d x).val)=form x) ∧
      (∀ k, k<dest ∨ dest+n^d≤k → val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r∉pairReadScratch → t.vars r=s.vars r) ∧
      t.arrs formOutputTape=s.arrs formOutputTape ∧ t.inp=s.inp ∧ t.out=s.out := by
  let u := s.setVar publicFormStart start
  let v := u.setVar publicFormTarget dest
  have hm : 0 < n^d := pow_pos hn _
  have hTo : pairFormTo right≠publicFormStart := by cases right <;> decide
  have r₀ : Run B (.assign publicFormStart (.var (pairFormFrom right))) s u 2 :=
    Run.assign (ev_var hStart (by omega))
  have r₁ : Run B (.assign publicFormTarget (.var (pairFormTo right))) u v 2 :=
    Run.assign (ev_var (by simpa [u,hTo] using hDest) (by have := hs.slots_word; omega))
  have hsv : Slots F canonical qN.WS S B v :=
    Slots.setVar F canonical (Slots.setVar F canonical hs (by decide) (by decide) _)
      (by decide) (by decide) _
  have hvReg {r : String} (h₁ : r≠publicFormStart) (h₂ : r≠publicFormTarget) :
      v.vars r=s.vars r := by simp [v,u,h₁,h₂]
  obtain ⟨t,rr,ht,hData,hOutside,hReg,hTape,hInp,hOut⟩ :=
    scatterPublicForm_run D F formOutputTape (by decide) form hn hnB hdB hmB hQ hFit hReadFit
      hsv (by simp [v,u,show publicFormStart≠publicFormTarget by decide]) rfl
      ((hvReg (by decide) (by decide)).trans hLen)
      ((hvReg (by decide) (by decide)).trans hModes)
      ((hvReg (by decide) (by decide)).trans hRadix) hRead
  refine ⟨t,(r₀.seq (r₁.seq rr)).mono (by omega),ht,hData,?_,?_,hTape,hInp,hOut⟩
  · intro k hk
    exact (hOutside k hk).trans ((val_setVar F canonical (by decide : publicFormTarget≠qN.WS) u dest k).trans
      (val_setVar F canonical (by decide : publicFormStart≠qN.WS) s start k))
  · intro r hr
    have h : r≠publicFormStart ∧ r≠publicFormTarget ∧ r≠publicFormCursor ∧ r∉scatterScratch := by
      simpa [pairReadScratch] using hr
    exact (hReg r h.2.2.1 h.2.2.2).trans (hvReg h.1 h.2.1)

noncomputable def scatterFormPair (D : FieldEncoding K) (F : FieldPresentation K) : Com :=
  .seq (scatterPairSide D F false) (scatterPairSide D F true)

/-- Replays two selected forms and protects every slot outside them. -/
theorem scatterFormPair_run (D : FieldEncoding K) (F : FieldPresentation K)
    {B S d n startL startR dstL dstR : ℕ} {s : Env}
    (f g : Coord d n → K) (hn : 0 < n) (hnB : n < B) (hdB : d < B) (hmB : n^d < B)
    (hQ : Fintype.card K ≤ B) (hApart : dstL+n^d≤dstR) (hFit : dstR+n^d≤S)
    (hFromL : startL+n^d≤B) (hFromR : startR+n^d≤B)
    (hs : Slots F canonical qN.WS S B s)
    (hStartL : s.vars (pairFormFrom false)=startL) (hStartR : s.vars (pairFormFrom true)=startR)
    (hDestL : s.vars (pairFormTo false)=dstL) (hDestR : s.vars (pairFormTo true)=dstR)
    (hLen : s.vars publicFormLength=n^d) (hModes : s.vars emitFormModes=d)
    (hRadix : s.vars reverseDigitBase=n)
    (hReadL : ∀ j : Fin (n^d), (s.arrs formOutputTape)[startL+j.val]? =
      some (D (f ((cutOrder d n).symm j))).val)
    (hReadR : ∀ j : Fin (n^d), (s.arrs formOutputTape)[startR+j.val]? =
      some (D (g ((cutOrder d n).symm j))).val) :
    ∃ t, Run B (scatterFormPair D F) s t (2*(4+scatterPublicFormCost F d (n^d))) ∧
      Slots F canonical qN.WS S B t ∧
      (∀ x, val F canonical qN.WS t (dstL+(inputCoordOrder n d x).val)=f x) ∧
      (∀ x, val F canonical qN.WS t (dstR+(inputCoordOrder n d x).val)=g x) ∧
      (∀ k, (k < dstL ∨ dstL+n^d ≤ k) → (k < dstR ∨ dstR+n^d ≤ k) →
        val F canonical qN.WS t k=val F canonical qN.WS s k) ∧
      (∀ r, r∉pairReadScratch → t.vars r=s.vars r) ∧
      t.arrs formOutputTape=s.arrs formOutputTape ∧ t.inp=s.inp ∧ t.out=s.out := by
  obtain ⟨u,ru,hu,hL,hMemL,hRegL,hTapeL,hInpL,hOutL⟩ :=
    scatterPairSide_run D F false f hn hnB hdB hmB hQ (by omega) hFromL hs hStartL hDestL
      hLen hModes hRadix hReadL
  obtain ⟨t,rt,ht,hR,hMemR,hRegR,hTapeR,hInpR,hOutR⟩ :=
    scatterPairSide_run D F true g hn hnB hdB hmB hQ hFit hFromR hu
      ((hRegL _ (by decide)).trans hStartR) ((hRegL _ (by decide)).trans hDestR)
      ((hRegL _ (by decide)).trans hLen) ((hRegL _ (by decide)).trans hModes)
      ((hRegL _ (by decide)).trans hRadix) (fun j => by rw [hTapeL]; exact hReadR j)
  refine ⟨t,(ru.seq rt).mono (by omega),ht,?_,hR,?_,?_,
    hTapeR.trans hTapeL,hInpR.trans hInpL,hOutR.trans hOutL⟩
  · intro x
    rw [hMemR _ (Or.inl (by have := (inputCoordOrder n d x).isLt; omega))]
    exact hL x
  · intro k h₁ h₂
    exact (hMemR _ h₂).trans (hMemL _ h₁)
  · intro r hr
    exact (hRegR r hr).trans (hRegL r hr)

#print axioms scatterPairSide_run
#print axioms scatterFormPair_run
end EvenTI.P19Install

