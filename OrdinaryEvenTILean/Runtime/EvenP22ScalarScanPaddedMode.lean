import EvenP22ScalarScanMappedSites
import EvenP22ScalarScanFirstReference
import EvenP21ScalarScanPublishLoop

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1450000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site EvenTI.P21Site.Mode
open EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad EvenTI.P21Pad
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites arrayWrites)

def paddedModeWithSites (widths mult : String) (right : Bool) : Com :=
  .seq (mappedModeSites widths mult) (prepareMaskedProbeStorage right)

/-- Read native sites from live archive words, mask the inverse-chart labels,
and commit the first retained reference to the same selected-mode record. -/
theorem paddedModeWithSites_run {W n blocks off base S width cutoff : ℕ} {s : Env}
    (widths mult : String) (right : Bool) (w e : ℕ → ℕ) (p : ScanModeInput W n)
    (chart : List ℕ) (first : Fin p.L)
    (rawSites : List ℕ) (h : MappedModeSitesInput widths mult W blocks off base S w e rawSites p.sites s)
    (hWidth : width < W) (hCut : cutoff < W)
    (hChart : s.arrs stencilChartBank=chart) (hWords : ∀ x ∈ chart, x < W)
    (hLength : chart.length=p.chart.length)
    (hLimit : s.vars stencilLimit=p.L) (hCols : s.vars stencilColumns=p.columns)
    (hMask : s.vars maskWidth=width) (hCutWord : s.vars maskCutoff=cutoff) (hZero : s.vars stencilZero=p.zero)
    (hExpected : ∀ j < p.L, p.chart.getD j 0=maskedWord right width cutoff p.zero chart j)
    (hTail : ∀ j, p.L ≤ j → p.chart.getD j 0=chart.getD j 0)
    (hFirstNZ : p.chart.getD first.val 0 ≠ p.zero)
    (hFirstPast : ∀ j < first.val, p.chart.getD j 0=p.zero)
    (hReference : p.reference.val=p.sites.getD (first.val/p.columns) 0) :
    ∃ t, Run W (paddedModeWithSites widths mult right) s t
      (mappedModeSitesCost w blocks+prepareMaskedProbeStorageCost p.L) ∧
      Frame (paddedModeWithSites widths mult right) s t ∧ ScanModeOutput p t := by
  obtain ⟨u,r₀,f₀,hSites,_,_⟩ := mappedModeSites_run widths mult w e rawSites p.sites h
  have hOne : 1 < W := by have := h.native.bound; omega
  have uChart : u.arrs stencilChartBank=chart :=
    (f₀.arrs _ (by change stencilChartBank ∉ arrayWrites (mappedModeSites "" ""); decide)).trans hChart
  have uL : u.vars stencilLimit=p.L :=
    (f₀.vars _ (by change stencilLimit ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hLimit
  have uCols : u.vars stencilColumns=p.columns :=
    (f₀.vars _ (by change stencilColumns ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hCols
  have uZ : u.vars stencilZero=p.zero :=
    (f₀.vars _ (by change stencilZero ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hZero
  have uMask : u.vars maskWidth=width :=
    (f₀.vars _ (by change maskWidth ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hMask
  have uCut : u.vars maskCutoff=cutoff :=
    (f₀.vars _ (by change maskCutoff ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hCutWord
  obtain ⟨v,r₁,f₁,masked,tail,vWords,_,_,_⟩ := applyPaddingMask_run right hOne p.wordL hWidth hCut p.wordZero
    (by rw [uChart,hLength]; exact p.fitChart) (by rwa [uChart]) uL uMask uCut uZ
  have vChart : v.arrs stencilChartBank=p.chart := by
    apply List.ext_getElem (by rw [f₁.len stencilChartBank,uChart,hLength])
    intro j hj hj'
    rw [←List.getD_eq_getElem _ 0 hj,←List.getD_eq_getElem _ 0 hj']
    by_cases hJ : j < p.L
    · rw [masked j hJ,uChart,hExpected j hJ]
    · rw [tail j (by omega),uChart,hTail j (by omega)]
  have vSites : v.arrs stencilSitesBank=p.sites := (f₁.arrs _ (by cases right <;> decide)).trans hSites
  have vL : v.vars stencilLimit=p.L := (f₁.vars _ (by cases right <;> decide)).trans uL
  have vC : v.vars stencilColumns=p.columns := (f₁.vars _ (by cases right <;> decide)).trans uCols
  have vZ : v.vars stencilZero=p.zero := (f₁.vars _ (by cases right <;> decide)).trans uZ
  obtain ⟨t,r₂,f₂,arrays,ref⟩ := findPadReference_first_run hOne p.wordL p.wordColumns p.wordZero
    vL vC vZ (by rw [vChart]; exact p.fitChart) vWords (by rw [vSites]; exact p.fitSites)
    (by rw [vSites]; exact p.wordSites)
  rw [vChart,vSites] at ref
  have refExact : t.vars stencilReference=p.reference.val := by
    rcases ref with empty | ⟨k,hk,hkPast,hkNZ,hkRef⟩
    · exact False.elim (hFirstNZ (empty first.val first.isLt))
    · have he : k=first.val := by
        by_contra hn
        rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
        · exact hkNZ (hFirstPast k hlt)
        · exact hFirstNZ (hkPast first.val hgt)
      rw [he] at hkRef
      exact hkRef.trans hReference.symm
  have rr : Run W (paddedModeWithSites widths mult right) s t
      (mappedModeSitesCost w blocks+prepareMaskedProbeStorageCost p.L) := r₀.seq (r₁.seq r₂)
  exact ⟨t,rr,Frame.of_run rr,⟨(f₂.vars _ (by decide)).trans vL,
    (f₂.vars _ (by decide)).trans vC,(f₂.vars _ (by decide)).trans vZ,refExact,
    (congrFun arrays _).trans vChart,(congrFun arrays _).trans vSites⟩⟩

#print axioms paddedModeWithSites_run
end EvenTI.P21ScalarScan
