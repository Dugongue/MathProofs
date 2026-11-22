import EvenP20PadGeometry

set_option autoImplicit false
set_option maxHeartbeats 700000

namespace EvenTI.P21Pad

open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004
open Mathproof.Problem18IMPFieldLayout20261001 (scalarWrites arrayWrites)
open EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad

def prepareMaskedProbeStorage (right : Bool) : Com :=
  .seq (applyPaddingMask right) findPadReference

def prepareMaskedProbeStorageCost (L : ℕ) : ℕ :=
  (38*L+6)+(24*L+6)

private theorem maskWrites (right : Bool) : scalarWrites (applyPaddingMask right)={maskCursor} := by
  cases right <;> decide

private theorem maskBanks (right : Bool) : arrayWrites (applyPaddingMask right)={stencilChartBank} := by
  cases right <;> decide

/-- Prepare one durable padded-mode query. The separate multi-mode CRT
driver can consume the published masked chart and chosen live reference
without re-running either preparation loop. -/
theorem prepareMaskedProbeStorage_run (right : Bool)
    {W L columns width cutoff zero : ℕ} {s : Env}
    (chart sites : List ℕ)
    (hOne : 1 < W) (hL : L < W) (hCol : columns < W)
    (hWidth : width < W) (hCut : cutoff < W) (hZero : zero < W)
    (hChartFit : L ≤ chart.length) (hSiteFit : ∀ k < L, k/columns < sites.length)
    (hChartWords : ∀ a ∈ chart, a < W) (hSiteWords : ∀ a ∈ sites, a < W)
    (hChart : s.arrs stencilChartBank=chart) (hSites : s.arrs stencilSitesBank=sites)
    (hLimit : s.vars stencilLimit=L) (hCols : s.vars stencilColumns=columns)
    (hWidthWord : s.vars maskWidth=width) (hCutWord : s.vars maskCutoff=cutoff)
    (hZeroWord : s.vars stencilZero=zero)
    (hActive : ∃ k < L, columnKept right cutoff (k%width)=true ∧ chart.getD k 0≠zero) :
    ∃ (t : Env) (k : ℕ), Run W (prepareMaskedProbeStorage right) s t (prepareMaskedProbeStorageCost L) ∧
      Frame (prepareMaskedProbeStorage right) s t ∧
      (∀ j < L, (t.arrs stencilChartBank).getD j 0=maskedWord right width cutoff zero chart j) ∧
      (∀ a ∈ t.arrs stencilChartBank, a < W) ∧
      t.arrs stencilSitesBank=sites ∧
      t.vars stencilLimit=L ∧ t.vars stencilColumns=columns ∧ t.vars stencilZero=zero ∧
      k < L ∧ columnKept right cutoff (k%width)=true ∧ chart.getD k 0≠zero ∧
      t.vars stencilReference=sites.getD (k/columns) 0 := by
  obtain ⟨u,ru,fu,hMask,_,hMaskedWords,_,_,_⟩ :=
    applyPaddingMask_run right hOne hL hWidth hCut hZero
      (by rw [hChart]; exact hChartFit) (by rw [hChart]; exact hChartWords)
      hLimit hWidthWord hCutWord hZeroWord
  have regU (r : String) (hr : r≠maskCursor) : u.vars r=s.vars r :=
    fu.vars r (by rw [maskWrites]; simpa using hr)
  have hSitesU : u.arrs stencilSitesBank=sites :=
    (fu.arrs _ (by rw [maskBanks]; decide)).trans hSites
  have hFitU : L ≤ (u.arrs stencilChartBank).length := by
    rw [fu.len,hChart]
    exact hChartFit
  have active (j : ℕ) (hj : j<L) : (u.arrs stencilChartBank).getD j 0≠zero ↔
      columnKept right cutoff (j%width)=true ∧ chart.getD j 0≠zero := by
    rw [hMask j hj,hChart]
    cases hKeep : columnKept right cutoff (j%width) <;> simp [maskedWord,hKeep]
  obtain ⟨t,rt,ft,hArrays,hSelected⟩ :=
    findPadReference_run hOne hL hCol hZero ((regU _ (by decide)).trans hLimit)
      ((regU _ (by decide)).trans hCols) ((regU _ (by decide)).trans hZeroWord) hFitU hMaskedWords
      (by rw [hSitesU]; exact hSiteFit) (by rw [hSitesU]; exact hSiteWords)
  obtain ⟨k,hk,hNZ,hRef⟩ : ∃ k < L, (u.arrs stencilChartBank).getD k 0≠zero ∧
      t.vars stencilReference=(u.arrs stencilSitesBank).getD (k/columns) 0 := by
    rcases hSelected with hAll | h
    · obtain ⟨j,hj,h⟩ := hActive
      exact False.elim (((active j hj).mpr h) (hAll j hj))
    · exact h
  have hKeep := (active k hk).mp hNZ
  have r := ru.seq rt
  have frame := Frame.of_run r
  refine ⟨t,k,r,frame,?_,?_,?_,?_,?_,?_,hk,hKeep.1,hKeep.2,?_⟩
  · intro j hj
    rw [hArrays,hMask j hj,hChart]
  · rw [hArrays]; exact hMaskedWords
  · exact (congrFun hArrays _).trans hSitesU
  · exact (frame.vars _ (by cases right <;> decide)).trans hLimit
  · exact (frame.vars _ (by cases right <;> decide)).trans hCols
  · exact (frame.vars _ (by cases right <;> decide)).trans hZeroWord
  · rwa [hSitesU] at hRef

#print axioms prepareMaskedProbeStorage_run
end EvenTI.P21Pad
