import Resume51ContiguousLabels
import EvenP19ScalarInstalledProbe
import Mathproof.Meta.Problem18PairBoundaryCopy20261004
import Mathproof.Meta.P15GEInit20261007

set_option autoImplicit false
set_option maxHeartbeats 350000

namespace EvenTI.P20Scalar

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open EvenTI.P18Scalar (stencilSitesBank)
open Mathproof.Problem18IMPFieldLayout20261001
open Mathproof.Problem18IMPFieldPresentation20261001
open Mathproof.Problem18ClaudeIMPSlots20261001
open Mathproof.Problem18AllFormatRoot20260930 (FieldPresentation)
open Mathproof.Problem18PairBoundaryCopy20261004
open Mathproof.P15RecogIMPDot20261007 (qN)
open Mathproof.Problem17Active47 (activeCount)
open Problem17CellCRT46 (source4)

def installNativeSites : Com :=
  copyBlock source4 stencilSitesBank (.mul (.lit 4) (.var activeCount)) (.lit 0) (.lit 0)

/-- Paid installation of every literal native joint-cell incidence label.
The count is read from the live compact-cell counter, and all field/chart
banks and the original source labels survive the copy. -/
theorem installNativeSites_run {K : Type} [Field K] [Fintype K]
    (F : FieldPresentation K) {W Sn a : ℕ} {s : Env}
    (hSlots : Slots F canonical qN.WS Sn W s)
    (hCount : s.vars activeCount=a) (hFour : 4 < W) (hSize : 4*a < W)
    (hSrc : 4*a ≤ (s.arrs source4).length)
    (hDst : 4*a ≤ (s.arrs stencilSitesBank).length)
    (hValues : ∀ k < 4*a, (s.arrs source4).getD k 0 < W) :
    ∃ t, Run W installNativeSites s t (80*a+14) ∧
      Slots F canonical qN.WS Sn W t ∧
      (∀ k < 4*a, (t.arrs stencilSitesBank).getD k 0=(s.arrs source4).getD k 0) ∧
      (∀ k, 4*a ≤ k → (t.arrs stencilSitesBank).getD k 0=(s.arrs stencilSitesBank).getD k 0) ∧
      (∀ b, b ≠ stencilSitesBank → t.arrs b=s.arrs b) ∧
      (t.arrs stencilSitesBank).length=(s.arrs stencilSitesBank).length ∧
      Frame installNativeSites s t ∧ t.inp=s.inp ∧ t.out=s.out := by
  have ha : a < W := by omega
  have ec : (.mul (.lit 4) (.var activeCount) : Expr).evalB W s=some (4*a) :=
    evalB_bin (evalB_lit hFour) (evalB_var_iff.mpr ⟨hCount.symm,by rw [hCount]; exact ha⟩) hSize
  obtain ⟨t,rt,hCopy,hTail,hOther,hLength,hVars,hInp,hOut⟩ :=
    copyBlock_run (src:=source4) (dst:=stencilSitesBank)
      (cntE:=.mul (.lit 4) (.var activeCount)) (sbE:=.lit 0) (dbE:=.lit 0)
      (n:=4*a) (sourceBase:=0) (targetBase:=0) (by decide) s ec
      (evalB_lit (by omega)) (evalB_lit (by omega)) hSize (by omega) (by omega)
      (by simpa only [Nat.zero_add] using hSrc) (by simpa only [Nat.zero_add] using hDst)
      (by simpa only [Nat.zero_add] using hValues)
  have hRun : Run W installNativeSites s t (80*a+14) := by
    simpa only [installNativeSites,Expr.size,← Nat.mul_assoc,Nat.add_assoc] using rt
  have hSafe : ∀ x ∈ regNames canonical, x ∉ copyRegs := by decide
  have ht : Slots F canonical qN.WS Sn W t :=
    Mathproof.P15GEInit20261007.slots_frame F hSlots
      (hOther _ (by decide)) (hOther _ (by decide))
      (fun x hx => hVars x (hSafe x hx)) (hVars _ (by decide))
  refine ⟨t,hRun,ht,?_,?_,hOther,hLength,Frame.of_run hRun,hInp,hOut⟩
  · simpa only [Nat.zero_add] using hCopy
  · intro k hk
    exact hTail k (Or.inr (by simpa only [Nat.zero_add] using hk))

#print axioms installNativeSites_run
end EvenTI.P20Scalar