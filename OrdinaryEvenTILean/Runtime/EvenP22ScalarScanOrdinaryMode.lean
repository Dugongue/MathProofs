import EvenP22ScalarScanMappedSites
import EvenP21ScalarScanPublishLoop
import EvenP21ScalarScanUnpadded

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1100000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site EvenTI.P21Site.Mode
open EvenTI.P19Scalar.PrefixStencil
open EvenTI.P20Scalar (positiveSiteCount)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites)

def ordinaryModeWithSites (widths mult : String) : Com :=
  .seq (mappedModeSites widths mult) prepareUnpaddedMode

/-- Convert actual archive width and multiplicity words to an ordinary
mode record throughout the same execution. -/
theorem ordinaryModeWithSites_run {W n blocks off base S c : ℕ} {s : Env}
    (widths mult : String) (w e : ℕ → ℕ) (p : ScanModeInput W n)
    (rawSites : List ℕ) (h : MappedModeSitesInput widths mult W blocks off base S w e rawSites p.sites s)
    (hc : c < W) (hCap : s.vars selectorChartCapacity=c)
    (hBank : (s.arrs stencilChartBank).length=c)
    (hLimit : p.L=rowPrefix w blocks) (hCol : p.columns=1) (hZero : p.zero=1)
    (hRef : p.reference.val=(if 0 < rowPrefix w blocks then p.sites.getD 0 0 else 0))
    (hChart : p.chart=List.replicate c 0) :
    ∃ t, Run W (ordinaryModeWithSites widths mult) s t (mappedModeSitesCost w blocks+20*c+28) ∧
      Frame (ordinaryModeWithSites widths mult) s t ∧ ScanModeOutput p t ∧
      t.vars globalStart = base+rowPrefix (nativeCount w e) blocks := by
  obtain ⟨u,r₀,f₀,huSites,huCount,huGlobal⟩ := mappedModeSites_run widths mult w e rawSites p.sites h
  have huCap : u.vars selectorChartCapacity=c :=
    (f₀.vars _ (by change selectorChartCapacity ∉ scalarWrites (mappedModeSites "" ""); decide)).trans hCap
  obtain ⟨t,r₁,f₁,cols0,cols1,zeroWord,ref,chart,sites⟩ := prepareUnpaddedMode_run p.sites
    (by have := h.native.bound; omega) hc h.native.rowWord huCount huCap
    ((f₀.len _).trans hBank) huSites (h.length ▸ h.native.siteFit) p.wordSites
  have r : Run W (ordinaryModeWithSites widths mult) s t (mappedModeSitesCost w blocks+20*c+28) :=
    (r₀.seq r₁).mono (by omega)
  exact ⟨t,r,Frame.of_run r,⟨cols0.trans hLimit.symm,cols1.trans hCol.symm,
    zeroWord.trans hZero.symm,ref.trans hRef.symm,chart.trans hChart.symm,sites⟩,
    (f₁.vars _ (by decide)).trans huGlobal⟩

#print axioms ordinaryModeWithSites_run
end EvenTI.P21ScalarScan
