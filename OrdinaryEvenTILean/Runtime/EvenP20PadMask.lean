import EvenP19ScalarPrefixStencil
import EvenP18ScalarArrayWords
import Mathproof.Meta.P15DecideIMPRowKer20261007

set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 19000

namespace EvenTI.P20Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var ev_add ev_mul ev_div hmdg)
open Mathproof.P15DecideIMPRowKer20261007 (ev_sub)
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P18Scalar (arrayWords_of_run)

def maskCursor : String := "even.scalar.pad.cursor"
def maskWidth : String := "even.scalar.pad.width"
def maskCutoff : String := "even.scalar.pad.cutoff"

def columnKept (right : Bool) (cutoff column : ℕ) : Bool :=
  if right then decide (cutoff ≤ column) else decide (column < cutoff)

def maskedWord (right : Bool) (width cutoff zero : ℕ) (chart : List ℕ) (j : ℕ) : ℕ :=
  if columnKept right cutoff (j%width) then chart.getD j 0 else zero

private def maskColumnExpr : Expr :=
  .sub (.var maskCursor) (.mul (.div (.var maskCursor) (.var maskWidth)) (.var maskWidth))

private def maskColumnGuard : Cond := .lt maskColumnExpr (.var maskCutoff)

private def sourceWord (retain : Bool) : Expr :=
  if retain then .get stencilChartBank (.var maskCursor) else .var stencilZero

private def maskStore (retain : Bool) : Com :=
  .store stencilChartBank (.var maskCursor) (sourceWord retain)

private def maskOne (right : Bool) : Com :=
  .ite maskColumnGuard (maskStore (!right)) (maskStore right)

private def endMaskGuard : Cond := .lt (.var maskCursor) (.var stencilLimit)

private def maskStep (right : Bool) : Com :=
  .seq (maskOne right) (.assign maskCursor (.add (.var maskCursor) (.lit 1)))

def applyPaddingMask (right : Bool) : Com :=
  .seq (.assign maskCursor (.lit 0)) (.while endMaskGuard (maskStep right))

private theorem maskOne_run (right : Bool) {B j width cutoff zero old : ℕ} {s : Env}
    (hIndex : s.vars maskCursor=j) (hWidth : s.vars maskWidth=width) (hLimit : s.vars maskCutoff=cutoff)
    (hZero : s.vars stencilZero=zero) (hj : j < B) (hw : width < B) (hC : cutoff < B) (hz : zero < B)
    (hOld : (s.arrs stencilChartBank)[j]?=some old) (hO : old < B)
    (hFit : j < (s.arrs stencilChartBank).length) :
    Run B (maskOne right) s (s.setArr stencilChartBank j
      (if columnKept right cutoff (j%width) then old else zero)) 30 := by
  have ej := ev_var hIndex hj
  have ew := ev_var hWidth hw
  have ec := ev_var hLimit hC
  have ez := ev_var hZero hz
  have getOld : (Expr.get stencilChartBank (.var maskCursor)).evalB B s=some old :=
    evalB_get ej hOld hO
  have hQuot : j/width < B := (Nat.div_le_self _ _).trans_lt hj
  have hProduct : j/width*width < B := (Nat.div_mul_le_self _ _).trans_lt hj
  have hRem : j-j/width*width < B := (Nat.sub_le _ _).trans_lt hj
  have eRem := ev_sub ej (ev_mul (ev_div ej ew hQuot) ew hProduct) hRem
  rw [hmdg] at eRem
  have em : maskColumnExpr.evalB B s=some (j%width) := by
    simpa only [maskColumnExpr,Expr.sub,Expr.mul,Expr.div,Mathproof.P15RecogIMPProgram20261007.v] using eRem
  have eg := evalB_condLt em ec
  have store (retain : Bool) : Run B (maskStore retain) s
      (s.setArr stencilChartBank j (if retain then old else zero)) 5 := by
    have ee : (sourceWord retain).evalB B s=some (if retain then old else zero) := by
      cases retain
      · exact ez
      · exact getOld
    apply (Run.store ej ee hFit).mono
    cases retain <;> decide
  by_cases h : j%width < cutoff
  · have hh : maskColumnGuard.evalB B s=some true := by
      have ht : decide (j%width < cutoff)=true := by simp [h]
      rw [ht] at eg
      exact eg
    have hKeep : columnKept right cutoff (j%width)=(!right) := by
      cases right <;> simp [columnKept,h,Nat.not_le.mpr h]
    rw [hKeep]
    exact (Run.ite_true (d:=maskStore right) hh (store (!right))).mono (by decide)
  · have hh : maskColumnGuard.evalB B s=some false := by
      have ht : decide (j%width < cutoff)=false := by simp [h]
      rw [ht] at eg
      exact eg
    have hKeep : columnKept right cutoff (j%width)=right := by
      cases right <;> simp [columnKept,h,Nat.le_of_not_gt h]
    rw [hKeep]
    exact (Run.ite_false (c:=maskStore (!right)) hh (store right)).mono (by decide)

private structure MaskState (right : Bool) (s u : Env) (L width cutoff zero : ℕ) : Prop where
  cursor : u.vars maskCursor ≤ L
  limit : u.vars stencilLimit=L
  widthEq : u.vars maskWidth=width
  cutoffEq : u.vars maskCutoff=cutoff
  zeroEq : u.vars stencilZero=zero
  length : (u.arrs stencilChartBank).length=(s.arrs stencilChartBank).length
  segment : SegInv (s.arrs stencilChartBank) (u.arrs stencilChartBank) 0
    (u.vars maskCursor) (maskedWord right width cutoff zero (s.arrs stencilChartBank))
  other : ∀ a, a≠stencilChartBank → u.arrs a=s.arrs a
  input : u.inp=s.inp
  output : u.out=s.out

/-- Physically overwrite exactly one chart prefix with the support mask,
preserving its unused capacity, both tapes and every other bank. -/
theorem applyPaddingMask_run (right : Bool) {B L width cutoff zero : ℕ} {s : Env}
    (hOne : 1 < B) (hL : L < B) (hWidth : width < B) (hCutoff : cutoff < B) (hZ : zero < B)
    (hCap : L ≤ (s.arrs stencilChartBank).length) (hWords : ∀ v ∈ s.arrs stencilChartBank, v < B)
    (hLimit : s.vars stencilLimit=L) (hW : s.vars maskWidth=width) (hC : s.vars maskCutoff=cutoff)
    (hZero : s.vars stencilZero=zero) :
    ∃ t, Run B (applyPaddingMask right) s t (38*L+6) ∧
      Frame (applyPaddingMask right) s t ∧
      (∀ j < L, (t.arrs stencilChartBank).getD j 0=
        maskedWord right width cutoff zero (s.arrs stencilChartBank) j) ∧
      (∀ j, L ≤ j → (t.arrs stencilChartBank).getD j 0=(s.arrs stencilChartBank).getD j 0) ∧
      (∀ v ∈ t.arrs stencilChartBank, v < B) ∧
      t.inp=s.inp ∧ t.out=s.out ∧ t.vars maskCursor=L := by
  let z := s.setVar maskCursor 0
  let I (u : Env) := MaskState right s u L width cutoff zero
  let potential (u : Env) := L-u.vars maskCursor
  have rz : Run B (.assign maskCursor (.lit 0)) s z 2 := Run.assign (evalB_lit (by omega))
  have hz : z.vars maskCursor=0 := rfl
  have hzI : I z := by
    refine ⟨by rw [hz]; omega, hLimit,hW,hC,hZero,rfl,?_,fun _ _ => rfl,rfl,rfl⟩
    rw [hz]
    exact SegInv.zero _ _ _
  have guard (u : Env) (h : I u) :
      endMaskGuard.evalB B u=some (decide (u.vars maskCursor < L)) := by
    exact evalB_condLt (evalB_var (h.cursor.trans_lt hL)) (ev_var h.limit hL)
  have step (u : Env) (h : I u) (hg : endMaskGuard.evalB B u=some true) :
      ∃ v, Run B (maskStep right) u v 34 ∧ I v ∧ potential v < potential u := by
    rw [guard u h] at hg
    let j := u.vars maskCursor
    have hj : j < L := of_decide_eq_true (Option.some.inj hg)
    have hFit0 := hj.trans_le hCap
    have hFit : j < (u.arrs stencilChartBank).length := by rw [h.length]; exact hFit0
    have hOld : (u.arrs stencilChartBank).getD j 0=(s.arrs stencilChartBank).getD j 0 :=
      h.segment.outside j (Or.inr (by simp [j]))
    have hRead : (u.arrs stencilChartBank)[j]?=some ((s.arrs stencilChartBank).getD j 0) := by
      rw [List.getElem?_eq_getElem hFit,← List.getD_eq_getElem _ _ hFit,hOld]
    have hOldWord : (s.arrs stencilChartBank).getD j 0 < B := by
      rw [List.getD_eq_getElem _ _ hFit0]
      exact hWords _ (List.getElem_mem hFit0)
    let value := maskedWord right width cutoff zero (s.arrs stencilChartBank) j
    let x := u.setArr stencilChartBank j value
    let v := x.setVar maskCursor (j+1)
    have r₀ : Run B (maskOne right) u x 30 :=
      maskOne_run right rfl h.widthEq h.cutoffEq h.zeroEq (hj.trans hL) hWidth hCutoff hZ hRead hOldWord hFit
    have r₁ : Run B (.assign maskCursor (.add (.var maskCursor) (.lit 1))) x v 4 :=
      Run.assign (ev_add (ev_var (show x.vars maskCursor=j from rfl) (hj.trans hL))
        (evalB_lit hOne) ((Nat.succ_le_of_lt hj).trans_lt hL))
    have hv : v.vars maskCursor=j+1 := rfl
    refine ⟨v,r₀.seq r₁,?_,?_⟩
    · refine ⟨by rw [hv]; omega,h.limit,h.widthEq,h.cutoffEq,h.zeroEq,?_,?_,?_,h.input,h.output⟩
      · simpa only [v,x,arrs_setVar,arrs_setArr,if_true,List.length_set] using h.length
      · have hs := h.segment.step (by simpa only [Nat.zero_add] using hFit) rfl
        simpa only [v,x,arrs_setVar,arrs_setArr,vars_setVar,vars_setArr,if_true,hv,Nat.zero_add] using hs
      · intro a ha
        simpa only [v,x,arrs_setVar,arrs_setArr,ha,if_false] using h.other a ha
    · change L-(j+1) < L-j
      omega
  obtain ⟨t,rt,ht,hEnd⟩ := Run.while_count I potential 34
    (fun u hu => ⟨_,guard u hu⟩) step hzI
  rw [guard t ht] at hEnd
  have hDone : t.vars maskCursor=L :=
    le_antisymm ht.cursor (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hEnd)))
  have hPotential : potential z=L := by change L-z.vars maskCursor=L; rw [hz,Nat.sub_zero]
  have hGuardSize : endMaskGuard.size=3 := rfl
  have run : Run B (applyPaddingMask right) s t (38*L+6) := by
    apply (rz.seq rt).mono
    change 2+((1+endMaskGuard.size+34)*potential z+1+endMaskGuard.size) ≤ _
    rw [hGuardSize,hPotential]
    omega
  refine ⟨t,run,Frame.of_run run,?_,?_,arrayWords_of_run run stencilChartBank hWords,ht.input,ht.output,hDone⟩
  · intro j hj
    have hRead := ht.segment.inside j (by rwa [hDone])
    simpa only [Nat.zero_add] using hRead
  · intro j hj
    apply ht.segment.outside j
    right
    simpa only [Nat.zero_add,hDone] using hj

#print axioms applyPaddingMask_run
end EvenTI.P20Pad
