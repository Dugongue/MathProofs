import EvenP21SiteMode
import EvenP21ScalarScanSelect

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1200000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site EvenTI.P21Site.Mode
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P20Scalar (nativeSourceLabelBank nativeFreeBank positiveSiteCount)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

/-- The selected factor archive and the actual row-width table determine
all active site words. Tail words are fixed by the current allocation. -/
structure ModeSitesInput (widths mult : String) (W blocks off base S : ℕ)
    (w e : ℕ → ℕ) (sites : List ℕ) (s : Env) : Prop where
  bound : 2 < W
  blockWord : blocks < W
  rowWord : rowPrefix w blocks < W
  totalOrigins : base+rowPrefix (nativeCount w e) blocks ≤ S
  slotWord : 2*S+1 < W
  offsetWord : off+blocks < W
  widthFit : off+blocks ≤ (s.arrs widths).length
  multiplicityFit : blocks ≤ (s.arrs mult).length
  widthData : ∀ j < blocks, (s.arrs widths).getD (off+j) 0 = w j
  multiplicityData : ∀ j < blocks, (s.arrs mult).getD j 0 = e j
  multiplicityWord : ∀ j < blocks, e j < W
  labelFit : rowPrefix w blocks ≤ (s.arrs nativeSourceLabelBank).length
  flagFit : rowPrefix w blocks ≤ (s.arrs nativeFreeBank).length
  siteFit : rowPrefix w blocks ≤ sites.length
  siteLength : (s.arrs stencilSitesBank).length = sites.length
  widthLabel : widths ≠ nativeSourceLabelBank
  widthFlag : widths ≠ nativeFreeBank
  multLabel : mult ≠ nativeSourceLabelBank
  multFlag : mult ≠ nativeFreeBank
  blockLimit : s.vars modeBlockLimit = blocks
  globalOffset : s.vars globalStart = base
  widthOffset : s.vars physicalWidthOffset = off
  data : ∀ j < blocks, ∀ k < w j, sites.getD (rowPrefix w j+k) 0 =
    if e j = 1 then 2*(base+rowPrefix (nativeCount w e) j)+1 else 0
  tail : ∀ k, rowPrefix w blocks ≤ k → (s.arrs stencilSitesBank).getD k 0 = sites.getD k 0

def modeSitesCost (w : ℕ → ℕ) (blocks : ℕ) : ℕ :=
  (40*rowPrefix w blocks+104)*blocks+30*rowPrefix w blocks+40

/-- Compute actual native site words from the selected width/multiplicity
rows and pin down the whole output array, including its untouched tail. -/
theorem modeSitesInput_run {W blocks off base S : ℕ} {s : Env}
    (widths mult : String) (w e : ℕ → ℕ) (sites : List ℕ)
    (h : ModeSitesInput widths mult W blocks off base S w e sites s) :
    ∃ t, Run W (modeSites widths mult) s t (modeSitesCost w blocks) ∧
      Frame (modeSites widths mult) s t ∧ t.arrs stencilSitesBank = sites ∧
      t.vars positiveSiteCount = rowPrefix w blocks ∧
      t.vars globalStart = base+rowPrefix (nativeCount w e) blocks := by
  obtain ⟨t,r,hValues,hCount,hGlobal,hTail,f⟩ := modeSites_run widths mult s w e
    h.bound h.blockWord h.rowWord h.totalOrigins h.slotWord h.offsetWord h.widthFit h.multiplicityFit
    h.widthData h.multiplicityData h.multiplicityWord h.labelFit h.flagFit (by change rowPrefix w blocks ≤ (s.arrs stencilSitesBank).length; rw [h.siteLength]; exact h.siteFit)
    h.widthLabel h.widthFlag h.multLabel h.multFlag h.blockLimit h.globalOffset h.widthOffset
  refine ⟨t,r,f,?_,hCount,hGlobal⟩
  have eqWord (k : ℕ) : (t.arrs stencilSitesBank).getD k 0 = sites.getD k 0 := by
    by_cases hk : k < rowPrefix w blocks
    · obtain ⟨j,hj,hlo,hhi⟩ := interval_cover w blocks k hk
      have hk' : k-rowPrefix w j < w j := by omega
      have he : rowPrefix w j + (k-rowPrefix w j) = k := by omega
      rw [←he]
      exact (hValues j hj _ hk').trans (h.data j hj _ hk').symm
    · exact (hTail k (by omega)).trans (h.tail k (by omega))
  apply List.ext_getElem ((f.len stencilSitesBank).trans h.siteLength)
  intro i hi hi'
  rw [← List.getD_eq_getElem _ 0 hi,← List.getD_eq_getElem _ 0 hi']
  exact eqWord i

#print axioms modeSitesInput_run
end EvenTI.P21ScalarScan
