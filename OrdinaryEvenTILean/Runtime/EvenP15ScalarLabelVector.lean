import EvenP15ScalarLabels
import Mathproof.Meta.IMPAutoCore20261004

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 4000000

namespace EvenTI.P15Scalar

open EvenTI.Contract EvenTI.P15Trial
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18IMPFieldPresentation20261001 (slice)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def scalarCopySource : String := "even.scalar.copy.source"
def scalarCopyTarget : String := "even.scalar.copy.target"
def scalarCopyLength : String := "even.scalar.copy.length"
def scalarCopyIndex : String := "even.scalar.copy.index"

private def fieldSlotIndex : Expr := .add (.var scalarCopySource) (.var scalarCopyIndex)
private def wordDestination : Expr := .add (.var scalarCopyTarget) (.var scalarCopyIndex)
private def scalarCopyGuard : Cond := .lt (.var scalarCopyIndex) (.var scalarCopyLength)
private def advanceScalarCopy : Com := .assign scalarCopyIndex (.add (.var scalarCopyIndex) (.lit 1))

private noncomputable def scalarCopyStep (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) : Com :=
  .seq (.assign labelAddress (addr canonical ws fieldSlotIndex))
    (.seq (.assign scalarLabelDest wordDestination)
      (.seq (installScalarLabel D F) advanceScalarCopy))

noncomputable def installScalarLabels (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) : Com :=
  .seq (.assign scalarCopyIndex (.lit 0)) (.while scalarCopyGuard (scalarCopyStep D F ws))

def installScalarLabelsCost (F : FieldPresentation K) (m : ℕ) : ℕ :=
  (installScalarLabelCost F+20)*m+6

private theorem keepSlots_afterData {F : FieldPresentation K} {ws : String} {S B : ℕ} {s : Env}
    (h : Slots F canonical ws S B s) (i v : ℕ) :
    Slots F canonical ws S B (s.setArr "data" i v) := by
  let t := s.setArr "data" i v
  have hm : t.arrs canonical.mem = s.arrs canonical.mem := by
    simp [t,arrs_setArr,show canonical.mem ≠ "data" by decide]
  have hs : t.arrs canonical.scratch = s.arrs canonical.scratch := by
    simp [t,arrs_setArr,show canonical.scratch ≠ "data" by decide]
  obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩,hws,hfit,ha,hc,hsw⟩ := h
  refine ⟨⟨h1,h2,h3,h4,h5,?_,?_,?_,?_,?_,h11,h12⟩,hws,?_,ha,?_,hsw⟩
  · rw [hm]; exact h6
  · rw [hs]; exact h7
  · rw [hs]; exact h8
  · rw [hm]; exact h9
  · intro j
    rw [hm]; exact h10 j
  · rw [hm]; exact hfit
  · intro p hp j
    change (t.arrs canonical.mem).getD (s.vars ws+p*F.e+j.val) 0 < F.p
    rw [hm]
    exact hc p hp j

/-- Copy an entire recovered matrix into the resident scalar scanner bank
using the exact live field slots. The input/output tapes are untouched. -/
theorem installScalarLabels_run (D : FieldEncoding K) (F : FieldPresentation K)
    {ws : String} {W S a d m : ℕ} {s : Env}
    (hS : Slots F canonical ws S W s)
    (hWS : labelAddress ≠ ws ∧ scalarLabelDest ≠ ws ∧ scalarCopyIndex ≠ ws)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W) (h1 : 1 < W)
    (hA : s.vars scalarCopySource = a) (hD : s.vars scalarCopyTarget = d) (hM : s.vars scalarCopyLength = m)
    (hRead : a+m ≤ S) (hFit : d+m ≤ (s.arrs "data").length)
    (hSize : (s.arrs "data").length < W) :
    ∃ t, Run W (installScalarLabels D F ws) s t (installScalarLabelsCost F m) ∧
      Slots F canonical ws S W t ∧
      SegInv (s.arrs "data") (t.arrs "data") d m (fun j => (D (val F canonical ws s (a+j))).val) ∧
      (t.arrs "data").length = (s.arrs "data").length ∧
      (∀ k, k ≠ "data" → t.arrs k = s.arrs k) ∧
      t.inp = s.inp ∧ t.out = s.out ∧
      (∀ x, x ≠ labelAddress → x ≠ scalarLabelDest → x ≠ scalarCopyIndex → t.vars x = s.vars x) := by
  let digits := fun j => (D (val F canonical ws s (a+j))).val
  let I (t : Env) : Prop :=
    Slots F canonical ws S W t ∧ t.vars scalarCopyIndex ≤ m ∧
    (∀ x, x ≠ labelAddress → x ≠ scalarLabelDest → x ≠ scalarCopyIndex → t.vars x = s.vars x) ∧
    SegInv (s.arrs "data") (t.arrs "data") d (t.vars scalarCopyIndex) digits ∧
    (t.arrs "data").length = (s.arrs "data").length ∧
    (∀ k, k ≠ "data" → t.arrs k = s.arrs k) ∧ t.inp = s.inp ∧ t.out = s.out
  let V (t : Env) := m-t.vars scalarCopyIndex
  have hm : m < W := by omega
  have ha : a < W := by have := hS.slots_word; omega
  have hd : d < W := by omega
  have evv (t : Env) {x : String} {z : ℕ} (hx : t.vars x=z) (hz : z < W) :
      (Expr.var x).evalB W t = some z := evalB_var_iff.mpr ⟨hx.symm,hx ▸ hz⟩
  let s₀ := s.setVar scalarCopyIndex 0
  have r₀ : Run W (.assign scalarCopyIndex (.lit 0)) s s₀ 2 := Run.assign (evalB_lit (by omega))
  have hInit : I s₀ := by
    refine ⟨Slots.setVar F canonical hS (by decide) hWS.2.2 0,by simp [s₀],
      ?_,by simpa [s₀] using SegInv.zero (s.arrs "data") d digits,rfl,fun _ _ => rfl,rfl,rfl⟩
    intro x _ _ hx
    simp [s₀,hx]
  have guard (t : Env) (h : I t) : scalarCopyGuard.evalB W t =
      some (decide (t.vars scalarCopyIndex < m)) := by
    have hl := (h.2.2.1 scalarCopyLength (by decide) (by decide) (by decide)).trans hM
    exact evalB_condLt (evalB_var (by have := h.2.1; omega)) (evv t hl hm)
  have step (t : Env) (h : I t) (hg : scalarCopyGuard.evalB W t = some true) :
      ∃ u, Run W (scalarCopyStep D F ws) t u (installScalarLabelCost F+16) ∧ I u ∧ V u < V t := by
    rw [guard t h] at hg
    have hi : t.vars scalarCopyIndex < m := by simpa using hg
    let i := t.vars scalarCopyIndex
    obtain ⟨hSlots,_,hvars,hseg,hlen,hkeep,hIn,hOut⟩ := h
    have hSrc := (hvars scalarCopySource (by decide) (by decide) (by decide)).trans hA
    have hTgt := (hvars scalarCopyTarget (by decide) (by decide) (by decide)).trans hD
    have hsI : a+i < S := by omega
    have hdI : d+i < (t.arrs "data").length := by omega
    have ei : (Expr.var scalarCopyIndex).evalB W t = some i := evalB_var (by change i < W; omega)
    have ea : fieldSlotIndex.evalB W t = some (a+i) :=
      evalB_bin (op:=.add) (evv t hSrc ha) ei (hsI.trans hS.slots_word)
    have eb : wordDestination.evalB W t = some (d+i) :=
      evalB_bin (op:=.add) (evv t hTgt hd) ei (hdI.trans (by rwa [hlen]))
    let k := t.vars ws+(a+i)*F.e
    let u := t.setVar labelAddress k
    have r₁ : Run W (.assign labelAddress (addr canonical ws fieldSlotIndex)) t u 8 :=
      Run.assign (evalB_addr F canonical hSlots ea hsI)
    have eT : wordDestination.evalB W u = some (d+i) := by
      rw [show wordDestination.evalB W u = wordDestination.evalB W t from by
        apply evalB_setVar_noVar
        simp [NoVar,wordDestination,scalarCopyTarget,scalarCopyIndex,labelAddress]]
      exact eb
    let v := u.setVar scalarLabelDest (d+i)
    have r₂ : Run W (.assign scalarLabelDest wordDestination) u v 4 := Run.assign eT
    have hvSlots := Slots.setVar F canonical
      (Slots.setVar F canonical hSlots (by decide) hWS.1 k) (by decide) hWS.2.1 (d+i)
    have hL : v.vars labelAddress = v.vars ws+(a+i)*F.e := by
      simp [v,u,k,show labelAddress ≠ scalarLabelDest by decide,Ne.symm hWS.1,Ne.symm hWS.2.1]
    have hE : val F canonical ws v (a+i) = val F canonical ws s (a+i) := by
      rw [val_setVar F canonical hWS.2.1,val_setVar F canonical hWS.1]
      unfold val slice
      rw [hvars ws (Ne.symm hWS.1) (Ne.symm hWS.2.1) (Ne.symm hWS.2.2),
        hkeep canonical.mem (by decide)]
    let w := v.setArr "data" (d+i) (digits i)
    have r₃ : Run W (installScalarLabel D F) v w (installScalarLabelCost F) := by
      have hDest' : v.vars scalarLabelDest < (v.arrs "data").length := by simpa [v,u] using hdI
      have hCopy := installScalarLabel_run D F hvSlots hsI hQ hP hL
        (by change (t.arrs "data").length < W; rwa [hlen]) hDest'
      have hDstEq : v.vars scalarLabelDest = d+i := by simp [v]
      rw [hDstEq,hE] at hCopy
      exact hCopy
    let y := w.setVar scalarCopyIndex (i+1)
    have hCur : w.vars scalarCopyIndex=i := by
      simp [w,v,u,i,show scalarCopyIndex ≠ scalarLabelDest by decide,
        show scalarCopyIndex ≠ labelAddress by decide]
    have r₄ : Run W advanceScalarCopy w y 4 := Run.assign (evalB_bin (op:=.add)
      (evv w hCur (by omega)) (evalB_lit h1) (show i+1 < W by omega))
    have hStep : Run W (scalarCopyStep D F ws) t y (installScalarLabelCost F+16) :=
      (r₁.seq (r₂.seq (r₃.seq r₄))).mono (by omega)
    have hy : y.vars scalarCopyIndex=i+1 := by simp [y]
    refine ⟨y,hStep,⟨Slots.setVar F canonical (keepSlots_afterData hvSlots _ _) (by decide) hWS.2.2 _,
      by rw [hy]; omega,?_,?_,?_,?_,hIn,hOut⟩,?_⟩
    · intro x hx hy hz
      simp [y,w,v,u,hx,hy,hz,hvars x hx hy hz]
    · rw [hy]
      change SegInv (s.arrs "data") ((t.arrs "data").set (d+i) (digits i)) d (i+1) digits
      exact hseg.step hdI rfl
    · change ((t.arrs "data").set (d+i) (digits i)).length = _
      rw [List.length_set,hlen]
    · intro x hx
      simpa [y,w,v,u,hx] using hkeep x hx
    · simp only [V,hy]
      change m-(i+1) < m-i
      omega
  obtain ⟨t,r,h,hStop⟩ := Run.while_count I V (installScalarLabelCost F+16)
    (fun t h => ⟨_,guard t h⟩) step hInit
  have hN : t.vars scalarCopyIndex=m := by
    rw [guard t h] at hStop
    exact le_antisymm h.2.1 (Nat.le_of_not_gt (of_decide_eq_false (Option.some.inj hStop)))
  obtain ⟨ht,_,hvars,hseg,hlen,hkeep,hIn,hOut⟩ := h
  refine ⟨t,(r₀.seq r).mono ?_,ht,by simpa only [hN] using hseg,hlen,hkeep,hIn,hOut,hvars⟩
  change 2+((1+3+(installScalarLabelCost F+16))*m+1+3) ≤ _
  rw [show 1+3+(installScalarLabelCost F+16)=installScalarLabelCost F+20 by omega]
  simp [installScalarLabelsCost] <;> omega

#print axioms installScalarLabels_run
end EvenTI.P15Scalar