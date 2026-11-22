import EvenP22ScalarScanDispatch

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 950000

namespace EvenTI.P21ScalarScan

open EvenTI.P21Site.Mode EvenTI.P19Scalar.PrefixStencil EvenTI.P20Pad EvenTI.P21Pad
open Lax13Proofs.Imp Lax13Proofs.Reasoning Mathproof.IMPAuto20261004

/-- The physical branch installed by a selected raw mode initializer. Each
constructor gives exactly the data read by its executable mode producer. -/
inductive InstalledModePreparation (widths mult : String) {W n : ℕ}
    (p : ScanModeInput W n) (c C : ℕ) (s : Env) : Prop where
  | ordinary {blocks off base S : ℕ} (w e : ℕ → ℕ) (rawSites : List ℕ)
      (kind : s.vars scanPaddingKind=0)
      (sites : MappedModeSitesInput widths mult W blocks off base S w e rawSites p.sites s)
      (capWord : c < W) (cap : s.vars selectorChartCapacity=c)
      (bank : (s.arrs stencilChartBank).length=c)
      (limit : p.L=rowPrefix w blocks) (col : p.columns=1) (zero : p.zero=1)
      (ref : p.reference.val=(if 0 < rowPrefix w blocks then p.sites.getD 0 0 else 0))
      (chart : p.chart=List.replicate c 0)
      (clock : mappedModeSitesCost w blocks+20*c+28 ≤ C)
  | padded {blocks off base S width cutoff : ℕ} (right : Bool) (w e : ℕ → ℕ)
      (chart rawSites : List ℕ) (first : Fin p.L)
      (kind : s.vars scanPaddingKind=(if right then 2 else 1))
      (sites : MappedModeSitesInput widths mult W blocks off base S w e rawSites p.sites s)
      (widthWord : width < W) (cutWord : cutoff < W)
      (bank : s.arrs stencilChartBank=chart) (words : ∀ x ∈ chart, x < W)
      (chartLen : chart.length=p.chart.length)
      (limit : s.vars stencilLimit=p.L) (cols : s.vars stencilColumns=p.columns)
      (maskWidthWord : s.vars maskWidth=width) (maskCutWord : s.vars maskCutoff=cutoff)
      (zero : s.vars stencilZero=p.zero)
      (expected : ∀ j < p.L, p.chart.getD j 0=maskedWord right width cutoff p.zero chart j)
      (tail : ∀ j, p.L ≤ j → p.chart.getD j 0=chart.getD j 0)
      (nonzero : p.chart.getD first.val 0 ≠ p.zero)
      (past : ∀ j < first.val, p.chart.getD j 0=p.zero)
      (reference : p.reference.val=p.sites.getD (first.val/p.columns) 0)
      (clock : mappedModeSitesCost w blocks+prepareMaskedProbeStorageCost p.L ≤ C)

/-- Execute the actual selected ordinary or padded mode from installed raw
banks and return the exact chart record needed by the durable publisher. -/
theorem installedModePreparation_run {W n c C : ℕ} {s : Env}
    (widths mult : String) (p : ScanModeInput W n)
    (prep : InstalledModePreparation widths mult p c C s) :
    ∃ t, Run W (selectModePreparation widths mult) s t (C+8) ∧
      Frame (selectModePreparation widths mult) s t ∧ ScanModeOutput p t := by
  cases prep with
  | ordinary w e rawSites kind sites capWord cap bank limit col zero ref chart clock =>
    obtain ⟨t,r,_,out,_⟩ := ordinaryModeWithSites_run widths mult w e p rawSites sites
      capWord cap bank limit col zero ref chart
    have rr : Run W (ModePreparation widths mult 0) s t C := r.mono clock
    exact ⟨t,selectModePreparation_run widths mult p sites.native.bound (by decide) kind rr out⟩
  | padded right w e chart rawSites first kind sites widthWord cutWord bank words chartLen
      limit cols maskWidthWord maskCutWord zero expected tail nonzero past reference clock =>
    obtain ⟨t,r,_,out⟩ := paddedModeWithSites_run widths mult right w e p chart first rawSites sites
      widthWord cutWord bank words chartLen limit cols maskWidthWord maskCutWord zero
      expected tail nonzero past reference
    let k := if right then 2 else 1
    have hk : k ≤ 2 := by cases right <;> decide
    have rr : Run W (ModePreparation widths mult k) s t C := by
      cases right <;> simpa [k,ModePreparation] using r.mono clock
    exact ⟨t,selectModePreparation_run widths mult p sites.native.bound hk kind rr out⟩

#print axioms installedModePreparation_run
end EvenTI.P21ScalarScan
