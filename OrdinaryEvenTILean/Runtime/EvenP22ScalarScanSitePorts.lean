import EvenP22ScalarScanSiteInput
import EvenP20SweepAddress

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 850000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site EvenTI.P21Site.Mode
open EvenTI.P20Sweep (savedOffset)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.P15DecideIMPEGens20261007 (ev_var)

def sourceNativePrefixBank : String := "even.p22.scalar.select.native_prefixes"

def bindNativeSitePorts (archiveSize : String) : Com :=
  .seq (.assign modeBlockLimit (.var archiveSize))
    (.seq (.assign physicalWidthOffset (.var savedOffset))
      (.assign globalStart (.get sourceNativePrefixBank (.var scanModeCursor))))

/-- Rebind the selected site producer directly from the live archive count,
the saved-width offset, and this occurrence's native source prefix. -/
theorem bindNativeSitePorts_run {W blocks off base : ℕ} {s : Env} {modes : ℕ}
    (archiveSize : String) (i : Fin modes) (hCount : s.vars archiveSize=blocks)
    (hOffset : s.vars savedOffset=off) (hMode : s.vars scanModeCursor=i.val)
    (hFit : i.val < (s.arrs sourceNativePrefixBank).length)
    (hPrefix : (s.arrs sourceNativePrefixBank).getD i.val 0=base)
    (hModeWord : i.val < W) (hCountWord : blocks < W) (hOffsetWord : off < W) (hBaseWord : base < W) :
    ∃ t, Run W (bindNativeSitePorts archiveSize) s t 7 ∧
      Frame (bindNativeSitePorts archiveSize) s t ∧ t.vars modeBlockLimit=blocks ∧
      t.vars physicalWidthOffset=off ∧ t.vars globalStart=base := by
  let u := s.setVar modeBlockLimit blocks
  let v := u.setVar physicalWidthOffset off
  let t := v.setVar globalStart base
  have r₀ : Run W (.assign modeBlockLimit (.var archiveSize)) s u 2 :=
    Run.assign (ev_var hCount hCountWord)
  have hu : u.vars savedOffset=off := by
    simpa [u,show savedOffset ≠ modeBlockLimit by decide] using hOffset
  have r₁ : Run W (.assign physicalWidthOffset (.var savedOffset)) u v 2 :=
    Run.assign (ev_var hu hOffsetWord)
  have hv : v.vars scanModeCursor=i.val := by
    simpa [v,u,show scanModeCursor ≠ modeBlockLimit by decide,
      show scanModeCursor ≠ physicalWidthOffset by decide] using hMode
  have readPrefix : (Expr.get sourceNativePrefixBank (.var scanModeCursor)).evalB W v=some base := by
    apply evalB_get (ev_var hv hModeWord) _ hBaseWord
    change (s.arrs sourceNativePrefixBank)[i.val]?=some base
    rw [List.getElem?_eq_getElem hFit,←List.getD_eq_getElem _ _ hFit,hPrefix]
  have r₂ : Run W (.assign globalStart (.get sourceNativePrefixBank (.var scanModeCursor))) v t 3 :=
    Run.assign readPrefix
  have rr : Run W (bindNativeSitePorts archiveSize) s t 7 := r₀.seq (r₁.seq r₂)
  exact ⟨t,rr,Frame.of_run rr,by simp [t,v,u,show modeBlockLimit ≠ globalStart by decide,
    show modeBlockLimit ≠ physicalWidthOffset by decide],
    by simp [t,v,show physicalWidthOffset ≠ globalStart by decide],by simp [t]⟩

#print axioms bindNativeSitePorts_run
end EvenTI.P21ScalarScan
