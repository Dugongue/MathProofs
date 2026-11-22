import EvenP17RecoverSeek
import EvenP17RecoverDigitWindow

set_option autoImplicit false
set_option maxHeartbeats 1900000

namespace EvenTI.P17Recover

open EvenTI.Contract EvenTI.P10Scan EvenTI.PrimaryAlignment EvenTI.P15Trial
open EvenTI.P14Projection EvenTI.P12CountPre EvenTI.P12Compare
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical scalarWrites arrayWrites)
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val val_setVar regNames)
open Mathproof.P15GEInit20261007 (slots_frame)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def liveAnchorWidth : String := "even.recover.anchor.width"

private def readAnchorWidth : Com :=
  .assign liveAnchorWidth (.get "data" (.var anchorAxis.start))

noncomputable def loadSelectedAnchor (D : FieldEncoding K) (F : FieldPresentation K)
    (right : Bool) : Com :=
  .seq (selectAnchor right)
    (.seq readAnchorWidth (loadFieldWindow D F anchorAxis.start anchorAxis.stop 1))

private theorem freshFieldRegisters (right : Bool) :
    ∀ r ∈ regNames canonical, r ∉ scalarWrites (selectAnchor right) := by cases right <;> decide

/-- Compute the chosen anchor's physical field coordinates and width from
its native serialized trial record. The raw tensor words and both trial
sections remain available for later anchors and the final witness check. -/
theorem loadSelectedAnchor_run (D : FieldEncoding K) (F : FieldPresentation K)
    (z forms : List ℕ) (right : Bool) (anchors : List (NumberedAnchor K))
    (i : Fin anchors.length) {B S base : ℕ} {s : Env}
    (hSec : OperandSections z right (listW (anchors.map (numberedAnchorWords D))) forms s)
    (hiB : i.val < B) (hI : s.vars anchorWanted=i.val)
    (hS : Slots F canonical qN.WS S B s) (hQ : Fintype.card K ≤ B) (hB : 1 < B)
    (hLen : z.length < B) (hBank : s.arrs "data"=sentinelWords z)
    (hBase : s.vars loadBase=base) (hFit : base+(anchors.get i).width*(anchors.get i).width ≤ S) :
    let A := anchors.get i
    ∃ t, Run B (loadSelectedAnchor D F right) s t
      (19*i.val+22+(3+(11+encodedBankLoadCost F contiguousAddress (A.width*A.width)))) ∧
      Slots F canonical qN.WS S B t ∧ t.vars liveAnchorWidth=A.width ∧
      (∀ k : Fin (A.width*A.width),
        val F canonical qN.WS t (base+k.val) =
          A.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2) ∧
      (∀ j, j < base ∨ base+A.width*A.width ≤ j → val F canonical qN.WS t j=val F canonical qN.WS s j) ∧
      t.arrs "data"=sentinelWords z ∧ t.inp=s.inp ∧ t.out=s.out ∧
      (∀ r, r ≠ liveAnchorWidth → r ≠ inputBase → r ≠ loadLength → ¬loadChanges r →
        r ∉ scalarWrites (selectAnchor right) → t.vars r=s.vars r) := by
  let A := anchors.get i
  let values := List.ofFn fun k : Fin (A.width*A.width) =>
    A.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
  have hN : values.length=A.width*A.width := by simp [values]
  have hRows : i.val < (anchors.map (numberedAnchorWords D)).length := by simpa using i.isLt
  obtain ⟨u,p,q,ru,hWindow,hSingle,f⟩ := selectAnchor_run z forms right (anchors.map (numberedAnchorWords D))
    hSec hRows hiB hI hLen hB hBank
  have hRow : slice z p q=A.width::values.map (fun x => (D x).val) := by
    simpa [numberedAnchorWords,List.getElem_map,List.map_ofFn,Function.comp_def,A,values] using hSingle
  have hLen' := congrArg List.length hRow
  rw [slice_length z hWindow.bounds.2,List.length_cons,List.length_map,hN] at hLen'
  have hpq : p < q := by omega
  have hData : u.arrs "data"=sentinelWords z := (f.arrs _ (by cases right <;> decide)).trans hBank
  have hEntry : (u.arrs "data")[p]? = some A.width := by
    rw [hData]
    simpa using getWord_of_slice z hWindow.bounds.2 hRow (k:=0) (by simp)
  have hWidth : A.width < B := by have := Nat.le_mul_self A.width; have := hWindow.bounds.2; omega
  have hpB : p < B := (hpq.trans_le hWindow.bounds.2).trans hLen
  have hp : (Expr.var anchorAxis.start).evalB B u = some p :=
    evalB_var_iff.mpr ⟨hWindow.start.symm,hWindow.start ▸ hpB⟩
  let v := u.setVar liveAnchorWidth A.width
  have rv : Run B readAnchorWidth u v 3 := Run.assign (evalB_get hp hEntry hWidth)
  have hU : Slots F canonical qN.WS S B u := slots_frame F hS
    (f.arrs _ (by cases right <;> decide)) (f.arrs _ (by cases right <;> decide))
    (fun r hr => f.vars r (freshFieldRegisters right r hr)) (f.vars _ (by cases right <;> decide))
  have hV : Slots F canonical qN.WS S B v := Slots.setVar F canonical hU (by decide) (by decide) _
  have hBody : slice z (p+1) q=values.map (fun x => (D x).val) := by
    rw [slice_cons z hpq hWindow.bounds.2] at hRow
    exact (List.cons.inj hRow).2
  have hvp : v.vars anchorAxis.start=p := by simpa [v,anchorAxis,liveAnchorWidth] using hWindow.start
  have hvq : v.vars anchorAxis.stop=q := by simpa [v,anchorAxis,liveAnchorWidth] using hWindow.stop
  have hBaseU : u.vars loadBase=base := (f.vars _ (by cases right <;> decide)).trans hBase
  have hBaseV : v.vars loadBase=base := by simpa [v,loadBase,liveAnchorWidth] using hBaseU
  obtain ⟨t,rt,hSlots,hVal,hOutside,hVars,hArr,hIn,hOut⟩ :=
    loadFieldWindow_run D F z values anchorAxis.start anchorAxis.stop 1 hV hQ hB
      (by omega) hWindow.bounds.2 hLen hvp hvq (by decide) (by decide) (by decide) (by decide)
      hBaseV (by rw [hN]; omega) hBody hData
  rw [hN] at rt
  have hWidthT : t.vars liveAnchorWidth=A.width :=
    (hVars _ (by decide) (by decide) (by decide)).trans (by simp [v])
  have hUV (k : ℕ) : val F canonical qN.WS u k=val F canonical qN.WS s k := by
    unfold val Mathproof.Problem18IMPFieldPresentation20261001.slice
    rw [f.vars qN.WS (by cases right <;> decide),f.arrs canonical.mem (by cases right <;> decide)]
  refine ⟨t,ru.seq (rv.seq rt),hSlots,hWidthT,?_,?_,
    (hArr _ (by decide)).trans hData,
    hIn.trans (f.inp (by cases right <;> exact noRead_of_check rfl)),
    hOut.trans (f.out (by cases right <;> exact noWrite_of_check rfl)),?_⟩
  · intro k
    change val F canonical qN.WS t (base+k.val) =
      A.matrix (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    have hk : k.val < values.length := by rw [hN]; exact k.isLt
    simpa only [values,List.getElem_ofFn] using hVal k.val hk
  · intro k hk
    have hK := hOutside k (by rw [hN]; omega)
    exact hK.trans ((val_setVar F canonical (by decide : liveAnchorWidth ≠ qN.WS) u _ k).trans (hUV k))
  · intro r hr hi hl hc hn
    refine (hVars r hi hl hc).trans ?_
    simpa [v,hr] using f.vars r hn

#print axioms loadSelectedAnchor_run
end EvenTI.P17Recover
