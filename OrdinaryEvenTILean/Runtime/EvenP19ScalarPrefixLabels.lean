import EvenP18ScalarChartLabels
import EvenP15ScalarLabelVector
import EvenP18ScalarStencil
import Mathproof.Meta.Problem18P34AssemblyMatrixMemory20261003
import Mathproof.Meta.Problem18P36BoundaryRoutedController20261003

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace EvenTI.P19Scalar.PrefixLabels

open EvenTI.P18Scalar (stencilChartBank)
open EvenTI.Contract EvenTI.P15Trial EvenTI.P15Scalar
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18IMPFieldLayout20261001 (canonical)
open Mathproof.Problem18ClaudeIMPSlots20261001 (Slots val)
open Mathproof.Problem18P36BoundaryRoutedController20261003
  (renameCom renameEnv renameEnv_arrs renameEnv_vars renameEnv_symm rename_run)

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def chartLabelSwap : String ≃ String := Equiv.swap "data" stencilChartBank

private theorem chartLabelSwap_data : chartLabelSwap "data"=stencilChartBank := by simp [chartLabelSwap]
private theorem chartLabelSwap_mem : chartLabelSwap canonical.mem=canonical.mem := by decide
private theorem chartLabelSwap_scratch : chartLabelSwap canonical.scratch=canonical.scratch := by decide

private theorem chartLabelSlots {F : FieldPresentation K} {ws : String} {S W : ℕ} {s : Env}
    (h : Slots F canonical ws S W s) :
    Slots F canonical ws S W (renameEnv chartLabelSwap.symm s) := by
  let u := renameEnv chartLabelSwap.symm s
  have hm : u.arrs canonical.mem=s.arrs canonical.mem := by
    change s.arrs (chartLabelSwap canonical.mem)=_
    rw [chartLabelSwap_mem]
  have hs : u.arrs canonical.scratch=s.arrs canonical.scratch := by
    change s.arrs (chartLabelSwap canonical.scratch)=_
    rw [chartLabelSwap_scratch]
  obtain ⟨⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12⟩,hws,hfit,ha,hc,hsw⟩ := h
  refine ⟨⟨h1,h2,h3,h4,h5,?_,?_,?_,?_,?_,h11,h12⟩,hws,?_,ha,?_,hsw⟩
  · rw [hm]; exact h6
  · rw [hs]; exact h7
  · rw [hs]; exact h8
  · rw [hm]; exact h9
  · intro j; rw [hm]; exact h10 j
  · rw [hm]; exact hfit
  · intro p hp j
    change (u.arrs canonical.mem).getD (s.vars ws+p*F.e+j.val) 0 < F.p
    rw [hm]
    exact hc p hp j

noncomputable def installChartLabels (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) : Com :=
  renameCom chartLabelSwap (installScalarLabels D F ws)

/-- Materialize actual canonical field-memory chart entries directly into
the stencil's own bank. The original raw data bank is preserved. -/
theorem installChartLabels_run (D : FieldEncoding K) (F : FieldPresentation K)
    {ws : String} {W S a L : ℕ} {s : Env}
    (hSlots : Slots F canonical ws S W s)
    (hWS : labelAddress ≠ ws ∧ scalarLabelDest ≠ ws ∧ scalarCopyIndex ≠ ws)
    (hQ : Fintype.card K ≤ W) (hP : F.p < W) (hOne : 1 < W)
    (hA : s.vars scalarCopySource=a) (hD : s.vars scalarCopyTarget=0)
    (hL : s.vars scalarCopyLength=L) (hRead : a+L ≤ S)
    (hTarget : L ≤ (s.arrs stencilChartBank).length)
    (hWord : (s.arrs stencilChartBank).length < W) :
    ∃ t, Run W (installChartLabels D F ws) s t (installScalarLabelsCost F L) ∧
      Slots F canonical ws S W t ∧
      (∀ j < L, (t.arrs stencilChartBank).getD j 0=
        (D (val F canonical ws s (a+j))).val) ∧
      (t.arrs stencilChartBank).length=(s.arrs stencilChartBank).length ∧
      (∀ k, L ≤ k → (t.arrs stencilChartBank).getD k 0 = (s.arrs stencilChartBank).getD k 0) ∧
      (∀ b, b ≠ stencilChartBank → t.arrs b=s.arrs b) ∧
      t.inp=s.inp ∧ t.out=s.out := by
  let u := renameEnv chartLabelSwap.symm s
  have huData : u.arrs "data"=s.arrs stencilChartBank := by
    change s.arrs (chartLabelSwap "data")=_
    rw [chartLabelSwap_data]
  obtain ⟨v,rv,hvSlots,hSegment,hLength,hOther,hInput,hOutput,hVars⟩ :=
    installScalarLabels_run D F (s:=u) (chartLabelSlots hSlots) hWS hQ hP hOne
      hA hD hL hRead (by rw [huData]; omega) (by rw [huData]; exact hWord)
  let t := renameEnv chartLabelSwap v
  have hBack : renameEnv chartLabelSwap u=s := renameEnv_symm chartLabelSwap.symm s
  have rt : Run W (installChartLabels D F ws) s t (installScalarLabelsCost F L) := by
    have rr := rename_run chartLabelSwap rv
    simpa only [installChartLabels,t,hBack] using rr
  have hData : t.arrs stencilChartBank=v.arrs "data" := by
    change v.arrs (chartLabelSwap.symm stencilChartBank)=_
    have hh : chartLabelSwap.symm stencilChartBank="data" :=
      (chartLabelSwap.symm_apply_eq.mpr chartLabelSwap_data.symm)
    rw [hh]
  have hSame : chartLabelSwap.symm=chartLabelSwap := by simp [chartLabelSwap]
  have htSlots : Slots F canonical ws S W t := by
    have hh := chartLabelSlots hvSlots
    rw [hSame] at hh
    exact hh
  have huVal (b : ℕ) : val F canonical ws u b=val F canonical ws s b := by
    apply Mathproof.Problem18P34AssemblyMatrixMemory20261003.val_congr F s u ws rfl
    intro i hi
    change (s.arrs (chartLabelSwap canonical.mem)).getD _ 0=(s.arrs canonical.mem).getD _ 0
    rw [chartLabelSwap_mem]
  refine ⟨t,rt,htSlots,?_,?_,?_,?_,hInput,hOutput⟩
  · intro j hj
    rw [hData]
    have hh := hSegment.inside j hj
    simpa only [Nat.zero_add,huVal] using hh
  · rw [hData,hLength,huData]
  · intro k hk
    rw [hData,← huData]
    exact hSegment.outside k (Or.inr (by simpa only [Nat.zero_add] using hk))
  · intro b hb
    have hNot : chartLabelSwap.symm b ≠ "data" := by
      intro he
      apply hb
      exact (chartLabelSwap.apply_symm_apply b).symm.trans
        ((congrArg chartLabelSwap he).trans chartLabelSwap_data)
    change v.arrs (chartLabelSwap.symm b)=s.arrs b
    rw [hOther _ hNot]
    simp only [u,renameEnv_arrs,Equiv.symm_symm,Equiv.apply_symm_apply]

theorem installChartLabels_eq (D : FieldEncoding K) (F : FieldPresentation K) (ws : String) :
    installChartLabels D F ws = EvenTI.P18Scalar.installChartLabels D F ws := rfl

#print axioms installChartLabels_run
end EvenTI.P19Scalar.PrefixLabels
